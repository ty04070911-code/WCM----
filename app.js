"use strict";
const APP_VERSION="25.0";

/* =========================================================
   Ver.12 Integrated Professional Monte Carlo Engine
   montecarlo-engine.js を app.js に統合
   ========================================================= */

/**
 * WCM Analyzer Pro - Monte Carlo Engine
 * Ver.12
 *
 * UIやDOMに依存しない独立シミュレーションエンジン。
 * 入力は日次単純リターン、内部計算は対数リターンで行う。
 */
const MonteCarloEngine=(()=>{
  const VERSION = "12.0.0";

  function assert(condition, message){
    if(!condition) throw new Error(message);
  }

  function clamp(value,min,max){
    return Math.min(Math.max(value,min),max);
  }

  function mean(values){
    return values.length
      ? values.reduce((sum,value)=>sum+value,0)/values.length
      : 0;
  }

  function variance(values,sample=true){
    if(values.length < (sample ? 2 : 1)) return 0;
    const average=mean(values);
    const divisor=sample ? values.length-1 : values.length;
    return values.reduce((sum,value)=>sum+(value-average)**2,0)/divisor;
  }

  function standardDeviation(values,sample=true){
    return Math.sqrt(Math.max(variance(values,sample),0));
  }

  function quantile(sortedValues,p){
    if(!sortedValues.length) return 0;
    const index=(sortedValues.length-1)*clamp(p,0,1);
    const lower=Math.floor(index);
    const upper=Math.ceil(index);
    if(lower===upper) return sortedValues[lower];
    return sortedValues[lower]+
      (sortedValues[upper]-sortedValues[lower])*(index-lower);
  }

  function skewness(values){
    if(values.length<3) return 0;
    const average=mean(values);
    const sd=standardDeviation(values,false);
    if(!sd) return 0;
    const m3=mean(values.map(v=>(v-average)**3));
    return m3/(sd**3);
  }

  function excessKurtosis(values){
    if(values.length<4) return 0;
    const average=mean(values);
    const sd=standardDeviation(values,false);
    if(!sd) return 0;
    const m4=mean(values.map(v=>(v-average)**4));
    return m4/(sd**4)-3;
  }

  function autocorrelation(values,lag=1){
    if(values.length<=lag) return 0;
    const average=mean(values);
    let numerator=0;
    let denominator=0;
    for(let i=0;i<values.length;i++){
      const centered=values[i]-average;
      denominator+=centered*centered;
      if(i>=lag){
        numerator+=centered*(values[i-lag]-average);
      }
    }
    return denominator ? numerator/denominator : 0;
  }

  function recommendedBlockLength(values){
    if(values.length<60) return 5;
    const rho1=Math.abs(autocorrelation(values,1));
    const rho5=Math.abs(autocorrelation(values,5));
    const persistence=clamp(rho1*.75+rho5*.25,0,0.95);
    const base=Math.cbrt(values.length);
    return Math.round(clamp(base*(1+6*persistence),5,63));
  }

  function makeRng(seed){
    let state=(Number(seed)||1)>>>0;
    return function(){
      state=(1664525*state+1013904223)>>>0;
      return state/4294967296;
    };
  }

  function normal(rng){
    let u=0;
    let v=0;
    while(!u) u=rng();
    while(!v) v=rng();
    return Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*v);
  }

  function gamma(shape,rng){
    assert(shape>0,"Gamma分布のshapeは0より大きくしてください。");
    if(shape<1){
      return gamma(shape+1,rng)*Math.pow(rng(),1/shape);
    }
    const d=shape-1/3;
    const c=1/Math.sqrt(9*d);
    while(true){
      const x=normal(rng);
      let v=1+c*x;
      if(v<=0) continue;
      v=v*v*v;
      const u=rng();
      if(u<1-.0331*x*x*x*x) return d*v;
      if(Math.log(u)<.5*x*x+d*(1-v+Math.log(v))) return d*v;
    }
  }

  function studentT(df,rng){
    const z=normal(rng);
    const chiSquare=2*gamma(df/2,rng);
    return z/Math.sqrt(chiSquare/df);
  }

  function winsorize(values,tailFraction){
    if(!tailFraction) return [...values];
    const sorted=[...values].sort((a,b)=>a-b);
    const low=quantile(sorted,tailFraction);
    const high=quantile(sorted,1-tailFraction);
    return values.map(v=>clamp(v,low,high));
  }

  function simpleToLogReturns(simpleReturns){
    return simpleReturns
      .filter(Number.isFinite)
      .filter(value=>value>-1)
      .map(value=>Math.log1p(value));
  }

  function applyDriftPolicy(logReturns,policy,shrinkage=.5){
    const historicalMean=mean(logReturns);
    let targetMean=historicalMean;

    if(policy==="shrink"){
      targetMean=historicalMean*clamp(shrinkage,0,1);
    }else if(policy==="zero"){
      targetMean=0;
    }else if(policy==="conservative"){
      targetMean=Math.min(historicalMean*.35,0);
    }

    const adjustment=targetMean-historicalMean;
    return {
      values:logReturns.map(value=>value+adjustment),
      historicalMean,
      targetMean
    };
  }

  function createIidSampler(series,rng){
    return ()=>series[Math.floor(rng()*series.length)];
  }

  function createMovingBlockSampler(series,blockSize,rng){
    let position=0;
    let block=[];

    return function(){
      if(position>=block.length){
        const size=Math.min(Math.max(1,blockSize),series.length);
        const maxStart=Math.max(series.length-size,0);
        const start=Math.floor(rng()*(maxStart+1));
        block=series.slice(start,start+size);
        position=0;
      }
      return block[position++];
    };
  }

  function createCircularBlockSampler(series,blockSize,rng){
    let index=0;
    let remaining=0;

    return function(){
      if(remaining<=0){
        index=Math.floor(rng()*series.length);
        remaining=Math.max(1,blockSize);
      }
      const value=series[index];
      index=(index+1)%series.length;
      remaining-=1;
      return value;
    };
  }

  function createRandomBlockSampler(series,minSize,maxSize,rng){
    let index=0;
    let remaining=0;
    const minimum=Math.max(1,minSize);
    const maximum=Math.max(minimum,maxSize);

    return function(){
      if(remaining<=0){
        index=Math.floor(rng()*series.length);
        remaining=minimum+
          Math.floor(rng()*(maximum-minimum+1));
      }
      const value=series[index];
      index=(index+1)%series.length;
      remaining-=1;
      return value;
    };
  }

  function createStationarySampler(series,averageBlockSize,rng){
    let index=Math.floor(rng()*series.length);
    const restartProbability=1/Math.max(1,averageBlockSize);

    return function(){
      if(rng()<restartProbability){
        index=Math.floor(rng()*series.length);
      }
      const value=series[index];
      index=(index+1)%series.length;
      return value;
    };
  }

  function createHybridSampler(series,blockSize,blockWeight,rng){
    const blockSampler=createStationarySampler(series,blockSize,rng);
    const iidSampler=createIidSampler(series,rng);
    const weight=clamp(blockWeight,0,1);
    return ()=>rng()<weight ? blockSampler() : iidSampler();
  }

  function createParametricSampler(series,distribution,df,rng){
    const average=mean(series);
    const sd=standardDeviation(series);
    if(distribution==="student-t"){
      const degrees=Math.max(3,df);
      const scale=sd*Math.sqrt((degrees-2)/degrees);
      return ()=>average+scale*studentT(degrees,rng);
    }
    return ()=>average+sd*normal(rng);
  }

  function createSampler(series,config,rng){
    switch(config.method){
      case "iid":
        return createIidSampler(series,rng);
      case "moving-block":
        return createMovingBlockSampler(series,config.blockSize,rng);
      case "circular-block":
        return createCircularBlockSampler(series,config.blockSize,rng);
      case "random-block":
        return createRandomBlockSampler(
          series,
          config.minBlockSize,
          config.maxBlockSize,
          rng
        );
      case "stationary":
        return createStationarySampler(
          series,
          config.averageBlockSize,
          rng
        );
      case "hybrid":
        return createHybridSampler(
          series,
          config.averageBlockSize,
          config.blockWeight,
          rng
        );
      case "normal":
        return createParametricSampler(series,"normal",null,rng);
      case "student-t":
        return createParametricSampler(
          series,
          "student-t",
          config.degreesOfFreedom,
          rng
        );
      default:
        throw new Error(`未対応のモンテカルロ手法です: ${config.method}`);
    }
  }

  function diagnose(simpleReturns,settings={}){
    const rawLogReturns=simpleToLogReturns(simpleReturns);
    assert(rawLogReturns.length>=30,"モンテカルロには30件以上の日次データが必要です。");

    const tailFraction=clamp(settings.winsorizeTail||0,0,.05);
    const cleaned=winsorize(rawLogReturns,tailFraction);
    const drift=applyDriftPolicy(
      cleaned,
      settings.driftPolicy||"shrink",
      settings.driftShrinkage??.5
    );

    const dailyMean=mean(drift.values);
    const dailyVol=standardDeviation(drift.values);
    const annualizedReturn=Math.expm1(dailyMean*252)*100;
    const annualizedVol=dailyVol*Math.sqrt(252)*100;
    const lag1=autocorrelation(drift.values,1);
    const lag5=autocorrelation(drift.values,5);
    const suggestedBlock=recommendedBlockLength(drift.values);

    const warnings=[];
    if(rawLogReturns.length<252) warnings.push("データ期間が1年未満です。");
    if(Math.abs(lag1)>.15) warnings.push("短期自己相関が比較的強く、単日抽出は流れを壊しやすいです。");
    if(excessKurtosis(drift.values)>3) warnings.push("裾が厚く、正規分布モデルは急落を過小評価しやすいです。");
    if(annualizedReturn>20) warnings.push("過去収益率が高いため、ドリフト縮小を推奨します。");
    if(settings.driftPolicy==="historical") warnings.push("過去平均をそのまま使うため、長期結果が楽観的になりやすいです。");

    return {
      count:drift.values.length,
      logReturns:drift.values,
      rawHistoricalDailyMean:drift.historicalMean,
      targetDailyMean:drift.targetMean,
      annualizedReturn,
      annualizedVol,
      skewness:skewness(drift.values),
      excessKurtosis:excessKurtosis(drift.values),
      lag1Autocorrelation:lag1,
      lag5Autocorrelation:lag5,
      suggestedBlockLength:suggestedBlock,
      warnings
    };
  }

  function normalizeConfig(config,diagnostics){
    const method=config.method||"stationary";
    const recommended=diagnostics.suggestedBlockLength;

    return {
      method,
      years:Math.max(1,Math.floor(config.years||5)),
      runs:Math.max(100,Math.floor(config.runs||1000)),
      seed:Number(config.seed)||1,
      startValue:Math.max(0,Number(config.startValue)||0),
      currentPrincipal:Math.max(0,Number(config.currentPrincipal)||0),
      monthlyContribution:Math.max(0,Number(config.monthlyContribution)||0),
      tradingDaysPerMonth:Math.max(1,Math.floor(config.tradingDaysPerMonth||21)),
      lossBasis:config.lossBasis||"total",
      blockSize:Math.max(1,Math.floor(config.blockSize||recommended)),
      minBlockSize:Math.max(1,Math.floor(config.minBlockSize||3)),
      maxBlockSize:Math.max(2,Math.floor(config.maxBlockSize||recommended*2)),
      averageBlockSize:Math.max(1,Math.floor(config.averageBlockSize||recommended)),
      blockWeight:clamp(config.blockWeight??.8,0,1),
      degreesOfFreedom:Math.max(3,Number(config.degreesOfFreedom)||5),
      captureYearly:config.captureYearly!==false
    };
  }

  function simulate(simpleReturns,config={},settings={}){
    const diagnostics=diagnose(simpleReturns,settings);
    const preparedSeries=diagnostics.logReturns;
    const normalized=normalizeConfig(config,diagnostics);

    assert(normalized.startValue>0,"開始時評価額が0以下です。");

    const totalMonths=normalized.years*12;
    const totalDays=totalMonths*normalized.tradingDaysPerMonth;
    const futureContributions=normalized.monthlyContribution*totalMonths;
    const threshold=normalized.lossBasis==="total"
      ?normalized.currentPrincipal+futureContributions
      :normalized.startValue;

    const outcomes=[];
    const maxDrawdowns=[];
    const yearly=Array.from({length:normalized.years},()=>[]);

    for(let runIndex=0;runIndex<normalized.runs;runIndex++){
      const rng=makeRng(normalized.seed+runIndex*104729);
      const sampler=createSampler(preparedSeries,normalized,rng);

      let value=normalized.startValue;
      let peak=value;
      let worstDrawdown=0;

      for(let dayIndex=1;dayIndex<=totalDays;dayIndex++){
        const logReturn=sampler();
        value*=Math.exp(logReturn);

        if(dayIndex%normalized.tradingDaysPerMonth===0){
          value+=normalized.monthlyContribution;
        }

        peak=Math.max(peak,value);
        if(peak>0){
          worstDrawdown=Math.min(worstDrawdown,value/peak-1);
        }

        if(
          normalized.captureYearly &&
          dayIndex%252===0
        ){
          const yearIndex=Math.min(
            Math.floor(dayIndex/252)-1,
            normalized.years-1
          );
          yearly[yearIndex].push(value);
        }
      }

      outcomes.push(value);
      maxDrawdowns.push(worstDrawdown);
    }

    outcomes.sort((a,b)=>a-b);
    maxDrawdowns.sort((a,b)=>a-b);

    const p01=quantile(outcomes,.01);
    const p05=quantile(outcomes,.05);
    const p25=quantile(outcomes,.25);
    const median=quantile(outcomes,.5);
    const p75=quantile(outcomes,.75);
    const p95=quantile(outcomes,.95);
    const p99=quantile(outcomes,.99);
    const average=mean(outcomes);
    const lossProbability=outcomes.filter(v=>v<threshold).length/
      normalized.runs*100;
    const severeLossProbability=outcomes.filter(v=>v<threshold*.8).length/
      normalized.runs*100;
    const expectedMedianReturn=(median/normalized.startValue-1)*100;

    return {
      engineVersion:VERSION,
      config:normalized,
      diagnostics,
      threshold,
      outcomes,
      yearly,
      maxDrawdowns,
      summary:{
        minimum:outcomes[0],
        p01,
        p05,
        p25,
        median,
        p75,
        p95,
        p99,
        maximum:outcomes.at(-1),
        average,
        lossProbability,
        severeLossProbability,
        expectedMedianReturn,
        medianMaxDrawdown:quantile(maxDrawdowns,.5)*100,
        severeMaxDrawdown:quantile(maxDrawdowns,.05)*100
      }
    };
  }

  function methodLabel(config){
    switch(config.method){
      case "iid": return "単日ブートストラップ";
      case "moving-block": return `移動ブロック法 ${config.blockSize}日`;
      case "circular-block": return `循環ブロック法 ${config.blockSize}日`;
      case "random-block": return `ランダム長 ${config.minBlockSize}〜${config.maxBlockSize}日`;
      case "stationary": return `定常ブートストラップ 平均${config.averageBlockSize}日`;
      case "hybrid": return `混合モデル ブロック${Math.round(config.blockWeight*100)}%`;
      case "normal": return "正規分布";
      case "student-t": return `t分布 自由度${config.degreesOfFreedom}`;
      default: return config.method;
    }
  }

  return Object.freeze({
    version:()=>VERSION,
    diagnose,
    simulate,
    methodLabel,
    recommendedBlockLength,
    autocorrelation
  });
})();

let distData=null,growthData=null,last={};
const $=id=>document.getElementById(id);
const yen=v=>new Intl.NumberFormat("ja-JP",{style:"currency",currency:"JPY",maximumFractionDigits:0}).format(Number(v||0));
const pct=v=>`${Number(v||0)>=0?"+":""}${Number(v||0).toFixed(2)}%`;
const fmt=d=>`${d.getFullYear()}/${String(d.getMonth()+1).padStart(2,"0")}/${String(d.getDate()).padStart(2,"0")}`;

function decode(buf){
  for(const e of ["shift-jis","utf-8"]){
    try{const t=new TextDecoder(e).decode(buf);if(t.includes("年月日")||t.includes("基準価額"))return t}catch(_){}
  }
  return new TextDecoder("utf-8").decode(buf)
}
function splitLine(line){
  let a=[],c="",q=false;
  for(let i=0;i<line.length;i++){
    const ch=line[i],n=line[i+1];
    if(ch=='"'&&q&&n=='"'){c+='"';i++}
    else if(ch=='"')q=!q;
    else if(ch==","&&!q){a.push(c.trim());c=""}
    else c+=ch
  }
  a.push(c.trim());return a
}
function num(v){const n=Number(String(v??"").replace(/,/g,"").replace(/[円¥￥\s]/g,""));return Number.isFinite(n)?n:NaN}
function date(v){
  const s=String(v||"").trim().replace(/[年月.\-]/g,"/").replace(/日/g,"");
  const p=s.split("/").map(Number);
  if(p.length>=3&&p.every(Number.isFinite))return new Date(p[0],p[1]-1,p[2]);
  if(/^\d{8}$/.test(s))return new Date(+s.slice(0,4),+s.slice(4,6)-1,+s.slice(6,8));
  const d=new Date(s);return isNaN(d)?null:d
}
function parse(text){
  const lines=text.replace(/\r\n?/g,"\n").split("\n").filter(x=>x.trim());
  let h=lines.findIndex(x=>x.includes("年月日")||x.toLowerCase().includes("date"));if(h<0)h=0;
  const rows=[];
  for(let i=h+1;i<lines.length;i++){
    const c=splitLine(lines[i]),d=date(c[0]),nav=num(c[1]);
    if(!d||!Number.isFinite(nav))continue;
    rows.push({date:d,dateText:fmt(d),nav,reinvestNav:num(c[2]),assets:num(c[3]),distribution:num(c[4])||0})
  }
  return rows.sort((a,b)=>a.date-b.date)
}
async function load(input,kind){
  const f=input.files[0],el=$(kind==="dist"?"distStatus":"growthStatus");if(!f)return;
  try{
    el.textContent="読み込み中…";
    const rows=parse(decode(await f.arrayBuffer()));
    if(rows.length<10)throw new Error("有効データが不足しています");
    if(kind==="dist")distData=rows;else growthData=rows;
    el.className="status ok";el.textContent=`${f.name}：${rows.length.toLocaleString()}件`;
    if(distData&&growthData){
      const s=new Date(Math.max(distData[0].date,growthData[0].date));
      if(!$("startDate").value)$("startDate").value=fmt(s).replaceAll("/","-");
      $("analyze").disabled=false;$("mainStatus").textContent="分析できます。"
    }
  }catch(e){el.className="status bad";el.textContent=`読込失敗：${e.message}`}
}
function mean(a){return a.reduce((s,v)=>s+v,0)/Math.max(a.length,1)}

function median(values){
  const clean=(values||[])
    .filter(Number.isFinite)
    .slice()
    .sort((left,right)=>left-right);

  if(!clean.length)return 0;

  const middle=Math.floor(clean.length/2);

  return clean.length%2
    ?clean[middle]
    :(clean[middle-1]+clean[middle])/2;
}
function sd(a){if(a.length<2)return 0;const m=mean(a);return Math.sqrt(a.reduce((s,v)=>s+(v-m)**2,0)/(a.length-1))}

function variance(values,sample=true){
  const clean=(values||[]).filter(Number.isFinite);
  if(clean.length<(sample?2:1))return 0;
  const average=mean(clean);
  const divisor=sample?clean.length-1:clean.length;
  return clean.reduce(
    (sum,value)=>sum+(value-average)**2,
    0
  )/divisor;
}

function skewness(values){
  const clean=(values||[]).filter(Number.isFinite);
  if(clean.length<3)return 0;
  const average=mean(clean);
  const sigma=Math.sqrt(variance(clean,false));
  if(!sigma)return 0;
  return mean(clean.map(value=>
    ((value-average)/sigma)**3
  ));
}

function excessKurtosis(values){
  const clean=(values||[]).filter(Number.isFinite);
  if(clean.length<4)return 0;
  const average=mean(clean);
  const sigma=Math.sqrt(variance(clean,false));
  if(!sigma)return 0;
  return mean(clean.map(value=>
    ((value-average)/sigma)**4
  ))-3;
}

function autocorrelation(values,lag=1){
  const clean=(values||[]).filter(Number.isFinite);
  if(clean.length<=lag||lag<1)return 0;
  const average=mean(clean);
  let numerator=0;
  let denominator=0;

  for(let index=0;index<clean.length;index++){
    const centered=clean[index]-average;
    denominator+=centered*centered;

    if(index>=lag){
      numerator+=centered*(clean[index-lag]-average);
    }
  }

  return denominator?numerator/denominator:0;
}

function returns(rows){const a=[];for(let i=1;i<rows.length;i++)if(rows[i-1].nav>0)a.push(rows[i].nav/rows[i-1].nav-1);return a}
function cagr(rows){const days=(rows.at(-1).date-rows[0].date)/86400000;return days>0?((rows.at(-1).nav/rows[0].nav)**(365.25/days)-1)*100:0}
function mdd(rows){let h=-Infinity,w=0;for(const r of rows){h=Math.max(h,r.nav);w=Math.min(w,r.nav/h-1)}return w*100}
function vol(rows){return sd(returns(rows))*Math.sqrt(252)*100}
function sharpe(rows){const r=returns(rows),s=sd(r);return s?mean(r)/s*Math.sqrt(252):0}

function downsideDeviation(rows,minimumAcceptableReturn=0){
  const r=returns(rows);
  if(!r.length)return 0;
  const downside=r.map(value=>Math.min(value-minimumAcceptableReturn,0));
  const variance=downside.reduce((sum,value)=>sum+value*value,0)/downside.length;
  return Math.sqrt(variance)
}
function sortino(rows,annualRiskFreeRate=0){
  const r=returns(rows);
  if(!r.length)return 0;
  const dailyTarget=annualRiskFreeRate/252;
  const downside=downsideDeviation(rows,dailyTarget);
  if(!downside)return 0;
  return (mean(r)-dailyTarget)/downside*Math.sqrt(252)
}
function historicalVar(rows,confidence=.95){
  const r=returns(rows).filter(Number.isFinite).sort((a,b)=>a-b);
  if(!r.length)return 0;
  const tailProbability=1-confidence;
  const cutoff=quantile(r,tailProbability);
  return Math.max(-cutoff,0)*100
}
function historicalCvar(rows,confidence=.95){
  const r=returns(rows).filter(Number.isFinite).sort((a,b)=>a-b);
  if(!r.length)return 0;
  const cutoff=quantile(r,1-confidence);
  const tail=r.filter(value=>value<=cutoff);
  if(!tail.length)return historicalVar(rows,confidence);
  return Math.max(-mean(tail),0)*100
}
function calmar(rows){
  const drawdown=Math.abs(mdd(rows));
  return drawdown>0?cagr(rows)/drawdown:0
}
function monthlyWin(rows){const m=new Map();rows.forEach(r=>m.set(`${r.date.getFullYear()}-${r.date.getMonth()}`,r.nav));const v=[...m.values()];let w=0;for(let i=1;i<v.length;i++)if(v[i]>v[i-1])w++;return v.length>1?w/(v.length-1)*100:0}
function normalizeExtraInvestments(items=[]){
  return (Array.isArray(items)?items:[])
    .map(item=>({date:String(item?.date||"").trim(),amount:Math.max(Number(item?.amount)||0,0)}))
    .filter(item=>/^\d{4}-\d{2}-\d{2}$/.test(item.date)&&item.amount>0)
    .sort((a,b)=>a.date.localeCompare(b.date));
}

function plan(rows,initial,monthly,day,extraInvestments=[]){
  const map=new Map();
  const appliedExtras=[];
  const ignoredExtras=[];
  if(initial>0)map.set(rows[0].dateText,initial);
  const g=new Map();rows.forEach(r=>{const k=`${r.date.getFullYear()}-${r.date.getMonth()+1}`;(g.get(k)||g.set(k,[]).get(k)).push(r)});
  [...g.values()].slice(1).forEach(rs=>{if(monthly<=0)return;const r=rs.find(x=>x.date.getDate()>=day)||rs.at(-1);map.set(r.dateText,(map.get(r.dateText)||0)+monthly)});

  const normalizedExtras=normalizeExtraInvestments(extraInvestments);
  for(const item of normalizedExtras){
    const target=new Date(item.date+"T00:00:00");
    if(target<rows[0].date){
      ignoredExtras.push({...item,reason:"分析開始日前"});
      continue;
    }
    const tradeRow=rows.find(r=>r.date>=target);
    if(!tradeRow){
      ignoredExtras.push({...item,reason:"CSV最終日より後"});
      continue;
    }
    map.set(tradeRow.dateText,(map.get(tradeRow.dateText)||0)+item.amount);
    appliedExtras.push({...item,tradeDate:tradeRow.dateText});
  }
  map.appliedExtras=appliedExtras;
  map.ignoredExtras=ignoredExtras;
  return map
}
function simDist(rows,initial,monthly,day,taxRate,extraInvestments=[]){
  const p=plan(rows,initial,monthly,day,extraInvestments),tm=1-taxRate/100;let ru=0,iu=0,principal=0,cash=0,tax=0;const h=[];
  for(const r of rows){
    const a=p.get(r.dateText)||0;if(a>0){const u=a/r.nav*10000;ru+=u;iu+=u;principal+=a}
    if(r.distribution>0){
      const gross=ru*r.distribution/10000,net=gross*tm;cash+=net;tax+=gross-net;
      const ri=iu*r.distribution/10000*tm;iu+=ri/r.nav*10000
    }
    const market=ru*r.nav/10000,total=market+cash,reinvest=iu*r.nav/10000;
    h.push({date:r.date,dateText:r.dateText,principal,market,cash,total,reinvest,tax})
  }
  return {principal,market:h.at(-1).market,cash,total:h.at(-1).total,reinvest:h.at(-1).reinvest,tax,history:h,appliedExtras:p.appliedExtras||[],ignoredExtras:p.ignoredExtras||[]}
}
function simGrowth(rows,initial,monthly,day,extraInvestments=[]){
  const p=plan(rows,initial,monthly,day,extraInvestments);let units=0,principal=0;const h=[];
  for(const r of rows){const a=p.get(r.dateText)||0;if(a>0){units+=a/r.nav*10000;principal+=a}h.push({date:r.date,dateText:r.dateText,principal,value:units*r.nav/10000})}
  return {principal,value:h.at(-1).value,history:h,appliedExtras:p.appliedExtras||[],ignoredExtras:p.ignoredExtras||[]}
}
function makeRng(seed){let state=(Number(seed)||1)>>>0;return function(){state=(1664525*state+1013904223)>>>0;return state/4294967296}}
function normalFromRng(rng){let u=0,v=0;while(!u)u=rng();while(!v)v=rng();return Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*v)}
function quantile(sorted,p){if(!sorted.length)return 0;const index=(sorted.length-1)*p,lo=Math.floor(index),hi=Math.ceil(index);return lo===hi?sorted[lo]:sorted[lo]+(sorted[hi]-sorted[lo])*(index-lo)}
function forecast(rows,days){
  const r=returns(rows).slice(-120),m=mean(r),s=sd(r),latest=rows.at(-1).nav;
  const center=latest*Math.exp(m*days),range=1.645*s*Math.sqrt(days);
  const low=latest*Math.exp(m*days-range),high=latest*Math.exp(m*days+range);
  const z=s?m*Math.sqrt(days)/s:0,up=50*(1+erf(z/Math.sqrt(2)));
  return {center,low,high,up}
}
function erf(x){const sign=x<0?-1:1;x=Math.abs(x);const a1=.254829592,a2=-.284496736,a3=1.421413741,a4=-1.453152027,a5=1.061405429,p=.3275911,t=1/(1+p*x);return sign*(1-(((((a5*t+a4)*t)+a3)*t+a2)*t+a1)*t*Math.exp(-x*x))}
function result(name,principal,value){const profit=value-principal;return{name,principal,value,profit,rate:principal?profit/principal*100:0}}

function lineChart(el,series){
  const all=series.flatMap(s=>s.values.filter(Number.isFinite));if(!all.length){el.innerHTML="";return}
  const min=Math.min(...all),max=Math.max(...all),w=760,h=290,p=38,span=max-min||1;
  const paths=series.map(s=>{
    const pts=s.values.map((v,i)=>`${p+i*(w-2*p)/Math.max(s.values.length-1,1)},${h-p-(v-min)*(h-2*p)/span}`).join(" ");
    return `<polyline fill="none" stroke="${s.color}" stroke-width="3" points="${pts}"/>`
  }).join("");
  const legend=series.map((s,i)=>`<text x="${p+i*170}" y="20" fill="${s.color}" font-size="13">${s.name}</text>`).join("");
  el.innerHTML=`<svg viewBox="0 0 ${w} ${h}" preserveAspectRatio="none"><rect width="100%" height="100%" fill="#f8fafc"/>${legend}<line x1="${p}" y1="${h-p}" x2="${w-p}" y2="${h-p}" stroke="#94a3b8"/><line x1="${p}" y1="${p}" x2="${p}" y2="${h-p}" stroke="#94a3b8"/>${paths}</svg>`
}

function percentileRank(values,current){
  const clean=values.filter(Number.isFinite).sort((a,b)=>a-b);
  if(!clean.length)return 50;
  let count=0;
  for(const v of clean)if(v<=current)count++;
  return count/clean.length*100
}
function rollingDrawdowns(rows){
  let high=-Infinity;
  return rows.map(r=>{
    high=Math.max(high,r.nav);
    return (r.nav/high-1)*100
  })
}
function recentReturn(rows,days){
  if(rows.length<2)return 0;
  const end=rows.at(-1).nav;
  const start=rows[Math.max(0,rows.length-1-days)].nav;
  return start>0?(end/start-1)*100:0
}
function clamp(value,min,max){return Math.min(Math.max(value,min),max)}
function calculateWcmScore(rows){
  const c=cagr(rows);
  const dd=mdd(rows);
  const v=vol(rows);
  const sh=sharpe(rows);
  const month=recentReturn(rows,21);
  const quarter=recentReturn(rows,63);
  const drawdowns=rollingDrawdowns(rows);
  const currentDd=drawdowns.at(-1);
  const ddRank=percentileRank(drawdowns,currentDd);

  let score=50;
  score+=clamp(c,-20,20)*1.1;
  score+=clamp(sh,-2,2)*9;
  score-=clamp(v-18,-10,25)*.7;
  score+=clamp(month,-15,15)*.7;
  score+=clamp(quarter,-25,25)*.35;
  score+=clamp(-currentDd,0,30)*.55;
  score=clamp(score,0,100);

  let label="様子見";
  if(score>=68)label="積立チャンス";
  if(score<38)label="警戒";

  return {score,label,c,dd,v,sh,month,quarter,currentDd,ddRank}
}
function inferDistributionProbabilities(rows){
  const paid=rows.filter(r=>r.distribution>0).map(r=>r.distribution);
  if(!paid.length)return [];
  const recent=paid.slice(-24);
  const freq={};
  recent.forEach(v=>freq[v]=(freq[v]||0)+1);
  const total=recent.length;
  return Object.entries(freq)
    .map(([value,count])=>({value:+value,probability:count/total*100,count}))
    .sort((a,b)=>b.probability-a.probability)
}
function estimateSpecialDistributionRisk(rows){
  const recentNav=rows.at(-1).nav;
  const allNav=rows.map(r=>r.nav);
  const rank=percentileRank(allNav,recentNav);
  const dd=rollingDrawdowns(rows).at(-1);
  let risk=50;
  risk+=clamp(50-rank,-40,40)*.7;
  risk+=clamp(-dd,0,35)*1.1;
  return clamp(risk,5,95)
}
function renderWcmDiagnosis(rows,results){
  const s=calculateWcmScore(rows);
  const best=[...results].sort((a,b)=>b.value-a.value)[0];
  const specialRisk=estimateSpecialDistributionRisk(rows);
  const distProbs=inferDistributionProbabilities(rows);
  const topDistribution=distProbs[0]?.value||0;

  $("scoreCards").innerHTML=`
    <div class="card"><div class="card-title">WCMスコア</div><div class="card-value">${s.score.toFixed(0)}/100</div><div class="card-sub">${s.label}</div></div>
    <div class="card"><div class="card-title">現在の下落率</div><div class="card-value">${s.currentDd.toFixed(2)}%</div></div>
    <div class="card"><div class="card-title">1か月騰落率</div><div class="card-value">${pct(s.month)}</div></div>
    <div class="card"><div class="card-title">特別分配リスク</div><div class="card-value">${specialRisk.toFixed(0)}%</div><div class="card-sub">参考推定</div></div>`;

  $("scoreGauge").innerHTML=`
    <div class="scorebar"><span style="width:${s.score}%"></span></div>
    <div class="small" style="margin-top:7px">0＝警戒　50＝中立　100＝積立好機</div>`;

  let signalClass="signal-watch";
  let signalText="通常積立を継続し、追加投資は急がない局面です。";
  if(s.label==="積立チャンス"){
    signalClass="signal-strong";
    signalText="過去データ上では、下落率と期待リターンのバランスが比較的良い局面です。通常積立の継続に加え、余裕資金での分割追加を検討できる水準です。"
  }else if(s.label==="警戒"){
    signalClass="signal-risk";
    signalText="値動きの不安定さが強く、短期的な下落継続に注意が必要です。追加投資は一括ではなく、複数回に分ける方が安全です。"
  }
  $("investmentSignal").className=`comment ${signalClass}`;
  $("investmentSignal").textContent=`判定：${s.label}

${signalText}

この判定は売買推奨ではなく、読み込んだ過去データを基にした統計評価です。`;

  const allDd=rollingDrawdowns(rows);
  const ddPercentile=percentileRank(allDd,s.currentDd);
  const navRank=percentileRank(rows.map(r=>r.nav),rows.at(-1).nav);
  $("marketPosition").innerHTML=`
    <div class="card"><div class="card-title">基準価額の過去順位</div><div class="card-value">${navRank.toFixed(1)}%</div><div class="card-sub">高いほど過去レンジ上部</div></div>
    <div class="card"><div class="card-title">下落率の過去順位</div><div class="card-value">${ddPercentile.toFixed(1)}%</div><div class="card-sub">低いほど深い下落</div></div>
    <div class="card"><div class="card-title">分配金最有力候補</div><div class="card-value">${topDistribution.toLocaleString()}円</div><div class="card-sub">${distProbs[0]?distProbs[0].probability.toFixed(1):"0.0"}%</div></div>
    <div class="card"><div class="card-title">今回最良方式</div><div class="card-value">${best.name}</div></div>`;

  const tone=s.score>=68?"強気寄り":s.score<38?"慎重":"中立";
  $("aiAdvisor").textContent=`総合判定は「${tone}」です。

WCMスコアは${s.score.toFixed(0)}点です。1か月騰落率は${s.month.toFixed(2)}%、3か月騰落率は${s.quarter.toFixed(2)}%、現在の最高値からの下落率は${s.currentDd.toFixed(2)}%です。

過去の分配実績からは、次回分配金の最有力候補は${topDistribution.toLocaleString()}円です。ただし、分配金は運用会社の判断で変更されるため、確定予測ではありません。

特別分配リスクは約${specialRisk.toFixed(0)}%と推定しました。ただし、実際の普通分配・特別分配は各投資家の個別元本で決まるため、この値は基準価額だけを使った参考値です。`
}
function stressScenarios(currentValue){
  return [
    {name:"調整局面",drop:-10,recovery:12,color:"#f59e0b"},
    {name:"2022年級",drop:-25,recovery:25,color:"#ef4444"},
    {name:"コロナ級",drop:-35,recovery:45,color:"#a855f7"},
    {name:"大暴落級",drop:-50,recovery:60,color:"#7f1d1d"}
  ].map(s=>{
    const bottom=currentValue*(1+s.drop/100);
    const recovered=bottom*(1+s.recovery/100);
    return {...s,bottom,recovered}
  })
}
function renderStress(){
  if(!last.ds)return;
  const current=last.ds.reinvest;
  const add=+$("crashAdd").value||0;
  const recovery=+$("recoveryRate").value||0;
  const scenarios=stressScenarios(current);

  $("stressCards").innerHTML=scenarios.map(s=>`
    <div class="card">
      <div class="card-title">${s.name}（${s.drop}%）</div>
      <div class="card-value">${yen(s.bottom)}</div>
      <div class="card-sub">想定回復後 ${yen(s.recovered)}</div>
    </div>`).join("");

  lineChart($("stressChart"),scenarios.map(s=>({
    name:s.name,color:s.color,values:[current,s.bottom,s.recovered]
  })));

  const crash=-25;
  const bottom=current*(1+crash/100);
  const unitsBoost=add>0?add/bottom:0;
  const noAddRecovered=bottom*(1+recovery/100);
  const addRecovered=(bottom+add)*(1+recovery/100);
  const advantage=addRecovered-noAddRecovered-add;

  $("stressComment").textContent=`想定下落率：${crash}%
暴落直後の評価額：${yen(bottom)}
追加投資額：${yen(add)}
その後${recovery}%回復した場合：${yen(addRecovered)}

追加投資による回復後の上乗せ効果は、単純計算で約${yen(Math.max(advantage,0))}です。実際には基準価額、約定日、分配金、税金で変わります。`
}
function sampleFireBootstrap(series,rng){
  if(!Array.isArray(series)||series.length===0)return 0;
  const index=Math.min(
    Math.floor(rng()*series.length),
    series.length-1
  );
  const value=series[index];
  return Number.isFinite(value)?value:0;
}

function fireMonteCarlo(){
  if(!last.d)return null;
  const currentAge=+$("currentAge").value||35;
  const targetAge=+$("targetAge").value||50;
  const years=Math.max(targetAge-currentAge,1);
  const months=years*12;
  const runs=1000;
  const monthly=+$("monthly").value||0;
  const need=+$("monthlyNeed").value||0;
  const wr=(+$("withdrawRate").value||4)/100;
  const target=need*12/wr;
  const series=returns(last.d).filter(Number.isFinite);
  const outcomes=[];
  for(let k=0;k<runs;k++){
    const rng=makeRng(700000+k*7919);
    let value=last.ds.reinvest;
    for(let m=0;m<months;m++){
      for(let d=0;d<21;d++)value*=Math.max(1+sampleFireBootstrap(series,rng),.001);
      value+=monthly
    }
    outcomes.push(value)
  }
  outcomes.sort((a,b)=>a-b);
  return {
    target,years,
    probability:outcomes.filter(v=>v>=target).length/runs*100,
    median:quantile(outcomes,.5),
    low:quantile(outcomes,.05),
    high:quantile(outcomes,.95)
  }
}

function createExtraInvestmentRow(item={}){
  const row=document.createElement("div");
  row.className="extra-invest-row";
  row.innerHTML=`
    <div class="field"><label>追加投資日</label><input class="extra-invest-date" type="date" value="${item.date||""}"></div>
    <div class="field"><label>追加投資額</label><input class="extra-invest-amount" type="number" min="0" step="1000" inputmode="numeric" value="${Number(item.amount)||""}" placeholder="例：100000"></div>
    <button type="button" class="gray extra-invest-delete">削除</button>`;
  row.querySelector(".extra-invest-delete").onclick=()=>{row.remove();saveExtraInvestments();updateExtraInvestStatus()};
  row.querySelectorAll("input").forEach(input=>input.addEventListener("change",()=>{saveExtraInvestments();updateExtraInvestStatus()}));
  $("extraInvestmentRows").appendChild(row);
  return row;
}

function getExtraInvestments(){
  return normalizeExtraInvestments([...document.querySelectorAll(".extra-invest-row")].map(row=>({
    date:row.querySelector(".extra-invest-date")?.value||"",
    amount:+(row.querySelector(".extra-invest-amount")?.value||0)
  })));
}

function saveExtraInvestments(){
  try{localStorage.setItem("wcm-extra-investments-v272",JSON.stringify(getExtraInvestments()))}catch(_){}
}

function loadExtraInvestments(){
  let items=[];
  try{items=JSON.parse(localStorage.getItem("wcm-extra-investments-v272")||"[]")}catch(_){}
  $("extraInvestmentRows").innerHTML="";
  normalizeExtraInvestments(items).forEach(createExtraInvestmentRow);
  updateExtraInvestStatus();
}

function updateExtraInvestStatus(applied=null,ignored=null){
  const el=$("extraInvestStatus");
  if(!el)return;
  const items=getExtraInvestments();
  if(applied!==null){
    const total=(applied||[]).reduce((s,x)=>s+x.amount,0);
    const ignoredCount=(ignored||[]).length;
    el.className=`status ${ignoredCount?"bad":"ok"}`;
    el.textContent=`追加投資 ${applied.length}件・${yen(total)}を計算へ反映${ignoredCount?` / 未反映 ${ignoredCount}件`:""}`;
    return;
  }
  if(!items.length){el.className="status";el.textContent="追加投資は未登録です。";return}
  el.className="status";
  el.textContent=`登録済み ${items.length}件・合計 ${yen(items.reduce((s,x)=>s+x.amount,0))}`;
}

function analyze(){
  try{
    const s=new Date($("startDate").value+"T00:00:00"),start=Math.max(s,distData[0].date,growthData[0].date),end=Math.min(distData.at(-1).date,growthData.at(-1).date);
    if(start>=end)throw new Error("共通期間がありません");
    const d=distData.filter(r=>r.date>=start&&r.date<=end),g=growthData.filter(r=>r.date>=start&&r.date<=end);
    const initial=+$("initial").value||0,monthly=+$("monthly").value||0,day=+$("day").value||1,tax=$("taxMode").value==="after"?(+$("taxRate").value||0):0;
    const extraInvestments=getExtraInvestments();
    if(initial<=0&&monthly<=0&&!extraInvestments.length)throw new Error("投資額を入力してください");
    const ds=simDist(d,initial,monthly,day,tax,extraInvestments),gs=simGrowth(g,initial,monthly,day,extraInvestments);
    saveExtraInvestments();
    updateExtraInvestStatus(ds.appliedExtras,ds.ignoredExtras);
    const rs=[result("分配金受取",ds.principal,ds.total),result("分配金再投資",ds.principal,ds.reinvest),result("資産成長型",gs.principal,gs.value)];
    last={d,g,ds,gs,rs};
    try{
      const autoDiagnosis=DataAdaptiveMode.diagnose(d.length);
      last.autoMode=autoDiagnosis;
      applyAutoModeToControls(autoDiagnosis);
      renderAutoMode(autoDiagnosis);
      $("autoModeStatus").className="status ok";
      $("autoModeStatus").textContent=`${d.length}営業日から${autoDiagnosis.current.label}を自動選択しました。`;
    }catch(error){
      console.warn("自動モード診断に失敗しました。",error);
    }
        $("adaptiveStatus").className="status";
    $("adaptiveStatus").textContent="分析データを更新しました。必要に応じてAdaptive AIを再学習してください。";
    $("statStatus").className="status";
    $("statStatus").textContent="分析データを更新しました。「統計予測を実行」を押してください。";
    $("measurementStatus").className="status";
    $("measurementStatus").textContent="分析データを更新しました。「予測精度を測定」を押してください。";
    $("advisorStatus").className="status";
    $("advisorStatus").textContent="分析データを更新しました。「総合判断を実行」を押してください。";
    $("regimeStatus").className="status";
    $("regimeStatus").textContent="分析データを更新しました。「相場局面を分析」を押してください。";
    $("backtestStatus").className="status";
    $("backtestStatus").textContent="分析データを更新しました。「精度検証を実行」を押してください。";
    renderWcmDiagnosis(d,rs);
    renderMonteDiagnostics();
    renderOutlook();
    buildMorningBrief();

    const best=[...rs].sort((a,b)=>b.value-a.value)[0];
    $("cards").innerHTML=`<div class="card"><div class="card-title">投資元本</div><div class="card-value">${yen(ds.principal)}</div></div><div class="card"><div class="card-title">最も高い方式</div><div class="card-value">${best.name}</div><div class="card-sub">${yen(best.value)}</div></div><div class="card"><div class="card-title">受取分配金</div><div class="card-value">${yen(ds.cash)}</div></div><div class="card"><div class="card-title">推定税額</div><div class="card-value">${yen(ds.tax)}</div></div>`;
    $("compareBody").innerHTML=rs.map(x=>`<tr><td>${x.name}</td><td>${yen(x.principal)}</td><td>${yen(x.value)}</td><td class="${x.profit>=0?"positive":"negative"}">${yen(x.profit)}</td><td>${pct(x.rate)}</td></tr>`).join("");
    $("riskBody").innerHTML=[
      ["CAGR",cagr(d),cagr(g),"%"],
      ["最大下落率",mdd(d),mdd(g),"%"],
      ["年率ボラティリティ",vol(d),vol(g),"%"],
      ["シャープレシオ",sharpe(d),sharpe(g),""],
      ["ソルティノレシオ",sortino(d),sortino(g),""],
      ["カルマーレシオ",calmar(d),calmar(g),""],
      ["日次VaR 95%",historicalVar(d,.95),historicalVar(g,.95),"%"],
      ["日次VaR 99%",historicalVar(d,.99),historicalVar(g,.99),"%"],
      ["日次CVaR 95%",historicalCvar(d,.95),historicalCvar(g,.95),"%"],
      ["月間勝率",monthlyWin(d),monthlyWin(g),"%"]
    ].map(x=>`<tr><td>${x[0]}</td><td>${x[1].toFixed(2)}${x[3]}</td><td>${x[2].toFixed(2)}${x[3]}</td></tr>`).join("");
    const fs=[["1か月",21],["3か月",63],["1年",252]];
    $("forecastCards").innerHTML=fs.map(([n,days])=>{const f=forecast(d,days);return`<div class="forecast"><span>${n}後</span><strong>${Math.round(f.center).toLocaleString()}円</strong><small>上昇確率 ${f.up.toFixed(1)}%<br>${Math.round(f.low).toLocaleString()}〜${Math.round(f.high).toLocaleString()}円</small></div>`}).join("");
    const paid=d.filter(r=>r.distribution>0).map(r=>r.distribution),freq={};paid.forEach(v=>freq[v]=(freq[v]||0)+1);const pred=Object.entries(freq).sort((a,b)=>b[1]-a[1]).slice(0,4);
    $("distributionForecast").innerHTML=pred.length?pred.map(([v,n])=>`<div class="card" style="margin-bottom:9px"><div class="card-title">${v}円</div><div class="progress"><span style="width:${n/paid.length*100}%"></span></div><div class="card-sub">${(n/paid.length*100).toFixed(1)}%</div></div>`).join(""):"分配実績がありません。";
    $("comment").textContent=`現在の統計判定は、1か月上昇確率${forecast(d,21).up.toFixed(1)}%です。\n\n比較期間では予想分配型CAGRが${cagr(d).toFixed(2)}%、資産成長型が${cagr(g).toFixed(2)}%でした。今回の条件では「${best.name}」が最も高い結果です。\n\n予想分配型の最大下落率は${mdd(d).toFixed(2)}%です。下落時にも積立を継続できる資金計画か確認してください。予測は過去データの延長であり、為替・金利・組入銘柄の業績を直接予測していません。`;
    const gh=new Map(gs.history.map(x=>[x.dateText,x]));const merged=ds.history.filter(x=>gh.has(x.dateText)).map(x=>({...x,growth:gh.get(x.dateText).value}));
    last.merged=merged;
    renderStress();
    lineChart($("assetChart"),[{name:"元本",color:"#64748b",values:merged.map(x=>x.principal)},{name:"受取",color:"#f59e0b",values:merged.map(x=>x.total)},{name:"再投資",color:"#3b82f6",values:merged.map(x=>x.reinvest)},{name:"成長型",color:"#22c55e",values:merged.map(x=>x.growth)}]);
    lineChart($("navChart"),[{name:"予想分配型",color:"#a855f7",values:d.map(x=>x.nav/d[0].nav*100)},{name:"資産成長型",color:"#22c55e",values:g.map(x=>x.nav/g[0].nav*100)}]);
    $("resultArea").hidden=false;$("mainStatus").className="status ok";$("mainStatus").textContent="分析完了";localStorage.setItem("wcm5",JSON.stringify({start:$("startDate").value,initial,monthly,day,taxMode:$("taxMode").value,taxRate:$("taxRate").value,extraInvestments}));
    $("resultArea").scrollIntoView({behavior:"smooth"})
  }catch(e){$("mainStatus").className="status bad";$("mainStatus").textContent=`分析エラー：${e.message}`}
}

function verifyMonteCarloEngine(){
  const required=[
    "simulate",
    "diagnose",
    "methodLabel",
    "recommendedBlockLength",
    "version"
  ];

  const missing=required.filter(
    name=>typeof MonteCarloEngine?.[name]!=="function"
  );

  if(missing.length){
    throw new Error(
      `モンテカルロエンジン初期化エラー: ${missing.join(", ")}`
    );
  }

  return true;
}

function getMonteSettings(){
  return {
    driftPolicy:$("mcDriftPolicy").value,
    driftShrinkage:.5,
    winsorizeTail:+$("mcWinsorize").value||0
  }
}

function getMonteConfig(methodOverride=null){
  const averageBlock=Math.max(2,+$("mcAverageBlock").value||20);
  const method=methodOverride||$("mcModel").value;

  return {
    method,
    years:+$("mcYears").value,
    runs:+$("mcRuns").value,
    seed:+$("mcSeed").value||1,
    startValue:last.ds.reinvest,
    currentPrincipal:last.ds.principal,
    monthlyContribution:+$("monthly").value||0,
    tradingDaysPerMonth:21,
    lossBasis:$("lossBasis").value,
    blockSize:averageBlock,
    minBlockSize:3,
    maxBlockSize:Math.min(63,Math.max(5,averageBlock*2)),
    averageBlockSize:averageBlock,
    blockWeight:clamp((+$("mcBlockWeight").value||80)/100,0,1),
    degreesOfFreedom:+$("mcDegreesFreedom").value||5,
    captureYearly:true
  }
}

function runProfessionalMonte(methodOverride=null){
  verifyMonteCarloEngine();
  if(!last.d)throw new Error("先にCSVを読み込み、分析を開始してください。");

  return MonteCarloEngine.simulate(
    returns(last.d),
    getMonteConfig(methodOverride),
    getMonteSettings()
  )
}

function renderMonteDiagnostics(){
  verifyMonteCarloEngine();
  if(!last.d)return;

  try{
    const diagnostics=MonteCarloEngine.diagnose(
      returns(last.d),
      getMonteSettings()
    );

    $("mcAverageBlock").value=diagnostics.suggestedBlockLength;

    const warningText=diagnostics.warnings.length
      ?`\n\n注意\n・${diagnostics.warnings.join("\n・")}`
      :"";

    $("mcDiagnostics").textContent=`モデル診断

日次データ：${diagnostics.count.toLocaleString()}件
年率換算リターン：${diagnostics.annualizedReturn.toFixed(2)}%
年率ボラティリティ：${diagnostics.annualizedVol.toFixed(2)}%
歪度：${diagnostics.skewness.toFixed(2)}
超過尖度：${diagnostics.excessKurtosis.toFixed(2)}
自己相関（1日）：${diagnostics.lag1Autocorrelation.toFixed(3)}
自己相関（5日）：${diagnostics.lag5Autocorrelation.toFixed(3)}
推奨平均ブロック長：${diagnostics.suggestedBlockLength}日${warningText}`;
  }catch(error){
    $("mcDiagnostics").textContent=`診断エラー：${error.message}`
  }
}

function renderSingleMonte(result){
  const summary=result.summary;
  const label=MonteCarloEngine.methodLabel(result.config);

  $("monteResult").innerHTML=`<div class="cards">
    <div class="card"><div class="card-title">下位1%</div><div class="card-value">${yen(summary.p01)}</div></div>
    <div class="card"><div class="card-title">下位5%</div><div class="card-value">${yen(summary.p05)}</div></div>
    <div class="card"><div class="card-title">中央値</div><div class="card-value">${yen(summary.median)}</div></div>
    <div class="card"><div class="card-title">上位5%</div><div class="card-value">${yen(summary.p95)}</div></div>
    <div class="card"><div class="card-title">元本割れ確率</div><div class="card-value">${summary.lossProbability.toFixed(1)}%</div><div class="card-sub">判定額 ${yen(result.threshold)}</div></div>
    <div class="card"><div class="card-title">中央値最大DD</div><div class="card-value">${summary.medianMaxDrawdown.toFixed(1)}%</div></div>
  </div>
  <div class="comment" style="margin-top:12px">モデル：${label}
エンジン：${result.engineVersion}
試行回数：${result.config.runs.toLocaleString()}回
ドリフト：${$("mcDriftPolicy").selectedOptions[0].textContent}
極端値調整：${$("mcWinsorize").selectedOptions[0].textContent}
25〜75%区間：${yen(summary.p25)}〜${yen(summary.p75)}
厳しい最大DD（下位5%）：${summary.severeMaxDrawdown.toFixed(1)}%</div>`;

  const buckets=28;
  const min=result.outcomes[0];
  const max=result.outcomes.at(-1);
  const counts=Array(buckets).fill(0);

  result.outcomes.forEach(value=>{
    const bucket=Math.min(
      buckets-1,
      Math.floor((value-min)/(max-min||1)*buckets)
    );
    counts[bucket]+=1;
  });

  lineChart(
    $("monteChart"),
    [{name:"最終資産分布",color:"#3b82f6",values:counts}]
  );

  const yearlyRows=result.yearly.map((values,index)=>{
    values.sort((a,b)=>a-b);
    return values.length
      ?`<tr><td>${index+1}年後</td><td>${yen(quantile(values,.05))}</td><td>${yen(quantile(values,.5))}</td><td>${yen(quantile(values,.95))}</td></tr>`
      :"";
  }).join("");

  $("yearlyMonte").innerHTML=`
    <div class="tablewrap">
      <table>
        <thead><tr><th>時点</th><th>下位5%</th><th>中央値</th><th>上位5%</th></tr></thead>
        <tbody>${yearlyRows}</tbody>
      </table>
    </div>
    <p class="small">過去データの再標本化に基づく参考シミュレーションです。将来を保証しません。</p>`;
}

function runMonte(){
  try{
    const result=runProfessionalMonte();
    renderSingleMonte(result);
  }catch(error){
    console.error(error);
    $("monteResult").innerHTML=
      `<div class="status bad">モンテカルロ実行エラー：${error.message}</div>`;
  }
}

function compareMonteMethods(){
  const status=$("monteCompareStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先に2つのCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  status.className="status";
  status.textContent="本格5手法を計算しています…";

  setTimeout(()=>{
    try{
      const methods=[
        "iid",
        "moving-block",
        "stationary",
        "random-block",
        "hybrid"
      ];

      const results=methods.map(method=>runProfessionalMonte(method));

      const cautious=[...results].sort(
        (a,b)=>a.summary.median-b.summary.median
      )[0];

      const highestRisk=[...results].sort(
        (a,b)=>b.summary.lossProbability-a.summary.lossProbability
      )[0];

      const consensusMedian=mean(results.map(r=>r.summary.median));
      const medianSpread=
        (Math.max(...results.map(r=>r.summary.median))-
         Math.min(...results.map(r=>r.summary.median)))/
        consensusMedian*100;

      $("monteCompareTable").innerHTML=`
        <div class="tablewrap">
          <table>
            <thead>
              <tr>
                <th>手法</th>
                <th>下位5%</th>
                <th>中央値</th>
                <th>上位5%</th>
                <th>元本割れ</th>
                <th>最大DD中央値</th>
              </tr>
            </thead>
            <tbody>
              ${results.map(result=>`
                <tr>
                  <td>${MonteCarloEngine.methodLabel(result.config)}</td>
                  <td>${yen(result.summary.p05)}</td>
                  <td>${yen(result.summary.median)}</td>
                  <td>${yen(result.summary.p95)}</td>
                  <td>${result.summary.lossProbability.toFixed(1)}%</td>
                  <td>${result.summary.medianMaxDrawdown.toFixed(1)}%</td>
                </tr>`).join("")}
            </tbody>
          </table>
        </div>`;

      let reliability;
      if(medianSpread<15){
        reliability="5手法の中央値が近く、モデル依存性は比較的小さいです。";
      }else if(medianSpread<35){
        reliability="手法による差があるため、中央値の平均と保守的手法を併せて確認してください。";
      }else{
        reliability="手法による差が非常に大きく、過去データの局面偏りが強い可能性があります。単一の結果を採用しないでください。";
      }

      $("monteCompareComment").textContent=`本格エンジン比較結果

5手法の中央値平均：
${yen(consensusMedian)}

最も保守的な中央値：
${MonteCarloEngine.methodLabel(cautious.config)}
${yen(cautious.summary.median)}

元本割れ確率が最も高い手法：
${MonteCarloEngine.methodLabel(highestRisk.config)}
${highestRisk.summary.lossProbability.toFixed(1)}%

手法間の中央値差：
${medianSpread.toFixed(1)}%

${reliability}

通常は、定常ブートストラップまたは混合モデルを中心に見て、単日抽出と移動ブロック法を上下の参考範囲として利用するのがおすすめです。`;

      status.className="status ok";
      status.textContent="本格5手法の比較が完了しました。";
    }catch(error){
      status.className="status bad";
      status.textContent=`比較エラー：${error.message}`;
    }
  },50);
}

function calcFire(){
  const status=$("fireStatus");
  const resultElement=$("fireResult");

  status.className="status";
  status.textContent="FIRE診断を計算しています…";
  resultElement.innerHTML="";

  setTimeout(()=>{
    try{
      if(!last.d||!last.ds){
        throw new Error("先にCSVを読み込み、「分析を開始」を押してください。");
      }

      const need=+$("monthlyNeed").value||0;
      const withdrawRate=(+$("withdrawRate").value||0)/100;
      const distributionYield=(+$("distributionYield").value||0)/100;
      const currentAge=+$("currentAge").value||0;
      const targetAge=+$("targetAge").value||0;

      if(need<=0){
        throw new Error("毎月必要な金額を1円以上で入力してください。");
      }
      if(withdrawRate<=0){
        throw new Error("想定年間取崩率を0より大きくしてください。");
      }
      if(distributionYield<=0){
        throw new Error("想定年間分配率を0より大きくしてください。");
      }
      if(targetAge<=currentAge){
        throw new Error("目標年齢は現在年齢より大きくしてください。");
      }

      const annual=need*12;
      const fire=annual/withdrawRate;
      const dist=annual/distributionYield;
      const current=last.ds.reinvest||0;
      const sim=fireMonteCarlo();

      if(!sim){
        throw new Error("シミュレーション用データを作成できませんでした。");
      }

      resultElement.innerHTML=`
        <div class="cards">
          <div class="card">
            <div class="card-title">取崩型必要資産</div>
            <div class="card-value">${yen(fire)}</div>
            <div class="card-sub">現在との差 ${yen(Math.max(fire-current,0))}</div>
          </div>
          <div class="card">
            <div class="card-title">分配金生活必要資産</div>
            <div class="card-value">${yen(dist)}</div>
            <div class="card-sub">現在との差 ${yen(Math.max(dist-current,0))}</div>
          </div>
          <div class="card">
            <div class="card-title">目標年齢での達成確率</div>
            <div class="card-value">${sim.probability.toFixed(1)}%</div>
            <div class="card-sub">${sim.years}年後</div>
          </div>
          <div class="card">
            <div class="card-title">目標時点の中央値</div>
            <div class="card-value">${yen(sim.median)}</div>
          </div>
        </div>
        <div class="comment" style="margin-top:12px">
目標資産：${yen(sim.target)}
下位5%：${yen(sim.low)}
中央値：${yen(sim.median)}
上位5%：${yen(sim.high)}

達成確率は過去の日次リターンを再抽出した1,000回の参考シミュレーションです。
        </div>`;

      status.className="status ok";
      status.textContent="FIRE診断が完了しました。";

      setTimeout(()=>{
        resultElement.scrollIntoView({
          behavior:"smooth",
          block:"start"
        });
      },80);
    }catch(error){
      console.error("FIRE診断エラー",error);
      status.className="status bad";
      status.textContent=`FIRE診断エラー：${error.message}`;
    }
  },50);
}

function download(){
  if(!last.merged)return;
  const rows=[["年月日","投資元本","受取型合計","再投資型","資産成長型","累計分配金","推定税額"],...last.merged.map(x=>[x.dateText,Math.round(x.principal),Math.round(x.total),Math.round(x.reinvest),Math.round(x.growth),Math.round(x.cash),Math.round(x.tax)])];
  const csv="\uFEFF"+rows.map(r=>r.map(v=>`"${String(v).replaceAll('"','""')}"`).join(",")).join("\n"),blob=new Blob([csv],{type:"text/csv"}),url=URL.createObjectURL(blob),a=document.createElement("a");a.href=url;a.download=`WCM_Ver5_${new Date().toISOString().slice(0,10)}.csv`;a.click();URL.revokeObjectURL(url)
}

function getMarketInputs(){
  return {
    nasdaq:+$("nasdaqChange").value||0,
    sp:+$("spChange").value||0,
    usdJpy:+$("usdJpyChange").value||0,
    vix:+$("vixChange").value||0,
    growth:+$("growthIndexChange").value||0,
    yieldBp:+$("yieldChange").value||0
  }
}
function calculateMarketScore(data){
  let score=50;
  score+=clamp(data.nasdaq,-10,10)*2.2;
  score+=clamp(data.sp,-8,8)*1.3;
  score+=clamp(data.growth,-10,10)*2.5;
  score+=clamp(data.usdJpy,-6,6)*1.2;
  score-=clamp(data.vix,-30,50)*.45;
  score-=clamp(data.yieldBp,-50,80)*.18;
  return clamp(score,0,100)
}
function analyzeMarketEnvironment(){
  const d=getMarketInputs();
  const score=calculateMarketScore(d);
  const reasons=[];
  const positives=[];
  const cautions=[];

  if(d.nasdaq<=-2)reasons.push(`NASDAQ100が${d.nasdaq.toFixed(1)}%下落し、成長株全体に売り圧力がかかっています。`);
  if(d.nasdaq>=2)positives.push(`NASDAQ100が${d.nasdaq.toFixed(1)}%上昇し、成長株に追い風です。`);

  if(d.growth<=-2)reasons.push(`世界成長株指数が${d.growth.toFixed(1)}%下落し、WCMの投資対象に逆風です。`);
  if(d.growth>=2)positives.push(`世界成長株指数が${d.growth.toFixed(1)}%上昇し、WCMの投資対象に追い風です。`);

  if(d.usdJpy<=-1.5)reasons.push(`ドル円が${d.usdJpy.toFixed(1)}%円高方向へ動き、円換算の基準価額を押し下げやすい環境です。`);
  if(d.usdJpy>=1.5)positives.push(`ドル円が${d.usdJpy.toFixed(1)}%円安方向へ動き、円換算の基準価額を支えやすい環境です。`);

  if(d.vix>=15)reasons.push(`VIXが${d.vix.toFixed(1)}%上昇し、投資家のリスク回避姿勢が強まっています。`);
  if(d.vix<=-10)positives.push(`VIXが${d.vix.toFixed(1)}%低下し、市場心理が改善しています。`);

  if(d.yieldBp>=15)reasons.push(`米10年金利が${d.yieldBp.toFixed(0)}bp上昇し、高PER成長株の評価に逆風です。`);
  if(d.yieldBp<=-15)positives.push(`米10年金利が${Math.abs(d.yieldBp).toFixed(0)}bp低下し、成長株の評価に追い風です。`);

  if(d.sp<=-2)cautions.push(`S&P500も${d.sp.toFixed(1)}%下落しており、個別要因より市場全体の影響が強い可能性があります。`);
  if(d.sp>=2)positives.push(`S&P500が${d.sp.toFixed(1)}%上昇し、米国株全体の地合いが良好です。`);

  let tone="中立";
  let className="market-neutral";
  if(score>=65){tone="追い風";className="market-positive"}
  if(score<40){tone="逆風";className="market-negative"}

  const mainText=[
    `総合判定：${tone}（外部環境スコア ${score.toFixed(0)}/100）`,
    "",
    reasons.length ? "主な下落要因\n・"+reasons.join("\n・") : "明確な大きな下落要因は入力値から確認できません。",
    "",
    positives.length ? "主な上昇要因\n・"+positives.join("\n・") : "",
    cautions.length ? "\n補足\n・"+cautions.join("\n・") : "",
    "",
    "この分析は入力した市場データから機械的に作成した参考コメントです。"
  ].filter(Boolean).join("\n");

  $("marketAnalysis").className=`comment ${className}`;
  $("marketAnalysis").textContent=mainText;

  $("marketScoreCards").innerHTML=`
    <div class="card"><div class="card-title">外部環境スコア</div><div class="card-value">${score.toFixed(0)}/100</div><div class="card-sub">${tone}</div></div>
    <div class="card"><div class="card-title">成長株要因</div><div class="card-value">${(d.nasdaq+d.growth).toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">為替要因</div><div class="card-value">${d.usdJpy>=0?"+":""}${d.usdJpy.toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">リスク要因</div><div class="card-value">${d.vix.toFixed(1)}%</div><div class="card-sub">VIX変化</div></div>`;

  localStorage.setItem("wcm8-market",JSON.stringify(d))
}
function restoreMarketInputs(){
  try{
    const d=JSON.parse(localStorage.getItem("wcm8-market")||"null");
    if(!d)return;
    $("nasdaqChange").value=d.nasdaq??0;
    $("spChange").value=d.sp??0;
    $("usdJpyChange").value=d.usdJpy??0;
    $("vixChange").value=d.vix??0;
    $("growthIndexChange").value=d.growth??0;
    $("yieldChange").value=d.yieldBp??0
  }catch(_){}
}


function getSavedMarketInputs(){
  try{
    return JSON.parse(localStorage.getItem("wcm8-market")||"null")||{
      nasdaq:0,sp:0,usdJpy:0,vix:0,growth:0,yieldBp:0
    }
  }catch(_){
    return {nasdaq:0,sp:0,usdJpy:0,vix:0,growth:0,yieldBp:0}
  }
}

function calculateExternalReturnAdjustment(market,weightPercent){
  const raw=
    market.nasdaq*.24+
    market.sp*.10+
    market.growth*.32+
    market.usdJpy*.16-
    market.vix*.035-
    market.yieldBp*.012;

  return raw*(clamp(weightPercent,0,100)/100)
}

function calculateCrashRisk(rows,market){
  const oneMonth=recentReturn(rows,21);
  const quarter=recentReturn(rows,63);
  const currentDd=rollingDrawdowns(rows).at(-1);
  const volatility=vol(rows);

  let risk=25;
  risk+=clamp(-oneMonth,0,20)*1.5;
  risk+=clamp(-quarter,0,30)*.65;
  risk+=clamp(-currentDd,0,40)*.8;
  risk+=clamp(volatility-18,0,35)*.85;
  risk+=clamp(market.vix,0,60)*.45;
  risk+=clamp(-market.nasdaq,0,12)*1.2;
  risk+=clamp(market.yieldBp,0,80)*.12;

  return clamp(risk,0,100)
}

function calculateActionSignal(rows,market){
  const wcm=calculateWcmScore(rows);
  const marketScore=calculateMarketScore(market);
  const crashRisk=calculateCrashRisk(rows,market);
  const recent=recentReturn(rows,21);

  let score=
    wcm.score*.55+
    marketScore*.25+
    (100-crashRisk)*.20;

  if(recent>12)score-=10;
  if(recent<-12)score+=8;

  score=clamp(score,0,100);

  let label="様子見";
  let code="hold";
  let detail="通常積立を続け、追加投資は急がない判定です。";

  if(score>=68){
    label="積立・分割追加";
    code="buy";
    detail="過去データと外部環境の組み合わせでは、通常積立の継続と分割追加を検討できる判定です。";
  }else if(score<38){
    label="慎重・利益確定も検討";
    code="take";
    detail="短期的な下落または過熱のリスクが高く、新規の一括投資は慎重にする判定です。保有比率が大きすぎる場合は一部利益確定も選択肢です。";
  }

  return {score,label,code,detail,wcm,marketScore,crashRisk}
}

function calculateOutlook(rows,market,weight,caution){
  const weekly=forecast(rows,5);
  const monthly=forecast(rows,21);
  const adjustment=calculateExternalReturnAdjustment(market,weight);

  let cautionFactor=1;
  if(caution==="cautious")cautionFactor=.65;
  if(caution==="optimistic")cautionFactor=1.25;

  const latest=rows.at(-1).nav;
  const weeklyAdjusted=weekly.center*(1+adjustment/100*.25*cautionFactor);
  const monthlyAdjusted=monthly.center*(1+adjustment/100*cautionFactor);

  const weeklyReturn=(weeklyAdjusted/latest-1)*100;
  const monthlyReturn=(monthlyAdjusted/latest-1)*100;

  const weeklyUp=clamp(weekly.up+adjustment*2.2,5,95);
  const monthlyUp=clamp(monthly.up+adjustment*1.6,5,95);

  return {
    latest,
    weekly:{...weekly,center:weeklyAdjusted,returnRate:weeklyReturn,up:weeklyUp},
    monthly:{...monthly,center:monthlyAdjusted,returnRate:monthlyReturn,up:monthlyUp},
    adjustment
  }
}

function outlookLabel(returnRate){
  if(returnRate>=2)return {label:"上昇寄り",className:"outlook-up"};
  if(returnRate<=-2)return {label:"下落寄り",className:"outlook-down"};
  return {label:"横ばい",className:"outlook-flat"}
}

function renderOutlook(){
  if(!last.d)return;

  const market=getMarketInputs();
  const weight=+$("marketWeight").value||40;
  const caution=$("forecastCaution").value;
  const outlook=calculateOutlook(last.d,market,weight,caution);
  const weeklyLabel=outlookLabel(outlook.weekly.returnRate);
  const monthlyLabel=outlookLabel(outlook.monthly.returnRate);
  const action=calculateActionSignal(last.d,market);
  const risk=action.crashRisk;

  $("outlookCards").innerHTML=`
    <div class="card">
      <div class="card-title">現在基準価額</div>
      <div class="card-value">${Math.round(outlook.latest).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">来週中心予測</div>
      <div class="card-value">${Math.round(outlook.weekly.center).toLocaleString()}円</div>
      <div class="card-sub">${pct(outlook.weekly.returnRate)}・上昇確率 ${outlook.weekly.up.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">来月中心予測</div>
      <div class="card-value">${Math.round(outlook.monthly.center).toLocaleString()}円</div>
      <div class="card-sub">${pct(outlook.monthly.returnRate)}・上昇確率 ${outlook.monthly.up.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">外部環境補正</div>
      <div class="card-value">${pct(outlook.adjustment)}</div>
      <div class="card-sub">入力値による参考補正</div>
    </div>`;

  $("outlookReason").className=`comment ${monthlyLabel.className}`;
  $("outlookReason").textContent=`来週判定：${weeklyLabel.label}
来月判定：${monthlyLabel.label}

来週の中心予測は${Math.round(outlook.weekly.center).toLocaleString()}円、来月は${Math.round(outlook.monthly.center).toLocaleString()}円です。

この予測は、CSVの過去リターンを基礎に、市場環境入力を${weight}%反映しています。相場ニュースや運用会社の判断を直接取得した予測ではありません。`;

  $("actionSignal").innerHTML=`
    <span class="signal-pill signal-${action.code}">${action.label}</span>

${action.detail}

総合行動スコア：${action.score.toFixed(0)}/100`;

  $("actionScore").innerHTML=`
    <div class="scorebar"><span style="width:${action.score}%"></span></div>
    <div class="small" style="margin-top:7px">
      WCM内部スコア ${action.wcm.score.toFixed(0)}点・外部環境 ${action.marketScore.toFixed(0)}点・暴落警戒度 ${action.crashRisk.toFixed(0)}点
    </div>`;

  const riskClass=risk>=65?"risk-high":risk>=40?"risk-mid":"risk-low";
  const riskLabel=risk>=65?"高い":risk>=40?"中程度":"低い";

  $("crashRiskCards").innerHTML=`
    <div class="card">
      <div class="card-title">暴落警戒度</div>
      <div class="card-value">${risk.toFixed(0)}/100</div>
      <div class="card-sub">${riskLabel}</div>
    </div>
    <div class="card">
      <div class="card-title">1か月騰落率</div>
      <div class="card-value">${pct(recentReturn(last.d,21))}</div>
    </div>
    <div class="card">
      <div class="card-title">現在下落率</div>
      <div class="card-value">${rollingDrawdowns(last.d).at(-1).toFixed(2)}%</div>
    </div>
    <div class="card">
      <div class="card-title">年率変動率</div>
      <div class="card-value">${vol(last.d).toFixed(2)}%</div>
    </div>`;

  $("crashRiskComment").className=`comment ${riskClass}`;
  $("crashRiskComment").textContent=risk>=65
    ?"過去データと入力した市場環境では、急落への警戒度が高めです。一括投資より分割投資を優先し、生活防衛資金を確保してください。"
    :risk>=40
      ?"警戒度は中程度です。通常積立を基本とし、追加投資は複数回に分ける方が安全です。"
      :"急落警戒度は比較的低い状態です。ただし、突発的なニュースによる下落は予測できません。";

  localStorage.setItem("wcm9-outlook",JSON.stringify({weight,caution}))
}

function restoreOutlookSettings(){
  try{
    const saved=JSON.parse(localStorage.getItem("wcm9-outlook")||"null");
    if(!saved)return;
    $("marketWeight").value=saved.weight??40;
    $("forecastCaution").value=saved.caution??"normal"
  }catch(_){}
}

function createSnapshot(){
  if(!last.d||!last.rs)return null;
  const market=getSavedMarketInputs();
  const action=calculateActionSignal(last.d,market);
  const outlook=calculateOutlook(
    last.d,
    market,
    +$("marketWeight").value||40,
    $("forecastCaution").value
  );
  const best=[...last.rs].sort((a,b)=>b.value-a.value)[0];

  return {
    id:Date.now(),
    date:new Date().toLocaleString("ja-JP"),
    latestNav:last.d.at(-1).nav,
    bestMethod:best.name,
    bestValue:best.value,
    action:action.label,
    actionScore:action.score,
    crashRisk:action.crashRisk,
    weeklyForecast:outlook.weekly.center,
    monthlyForecast:outlook.monthly.center
  }
}

function loadHistory(){
  try{return JSON.parse(localStorage.getItem("wcm9-history")||"[]")}
  catch(_){return []}
}

function saveSnapshot(){
  const snapshot=createSnapshot();
  if(!snapshot)return;
  const history=loadHistory();
  history.unshift(snapshot);
  localStorage.setItem("wcm9-history",JSON.stringify(history.slice(0,20)));
  renderHistory()
}

function renderHistory(){
  const history=loadHistory();
  $("historyList").innerHTML=history.length
    ?history.map(item=>`
      <div class="history-item">
        <div class="history-head">
          <span>${item.date}</span>
          <span>${item.action}</span>
        </div>
        <div class="history-meta">
          基準価額：${Math.round(item.latestNav).toLocaleString()}円<br>
          最良方式：${item.bestMethod}（${yen(item.bestValue)}）<br>
          行動スコア：${item.actionScore.toFixed(0)}点・暴落警戒度：${item.crashRisk.toFixed(0)}点<br>
          来週予測：${Math.round(item.weeklyForecast).toLocaleString()}円・来月予測：${Math.round(item.monthlyForecast).toLocaleString()}円
        </div>
      </div>`).join("")
    :'<div class="small">保存された履歴はありません。</div>'
}

function clearHistory(){
  if(confirm("分析履歴をすべて削除しますか？")){
    localStorage.removeItem("wcm9-history");
    renderHistory()
  }
}


function getLatestDistributionCandidates(rows){
  const paid=rows.filter(r=>r.distribution>0).map(r=>r.distribution);
  if(!paid.length)return [];
  const recent=paid.slice(-36);
  const weighted=new Map();

  recent.forEach((value,index)=>{
    const recencyWeight=.5+(index+1)/recent.length;
    weighted.set(value,(weighted.get(value)||0)+recencyWeight)
  });

  const total=[...weighted.values()].reduce((s,v)=>s+v,0);
  return [...weighted.entries()]
    .map(([value,weight])=>({
      value:+value,
      probability:total?weight/total*100:0
    }))
    .sort((a,b)=>b.probability-a.probability)
    .slice(0,4)
}

function calculateWcmIndex(rows,market){
  const internal=calculateWcmScore(rows);
  const marketScore=calculateMarketScore(market);
  const crashRisk=calculateCrashRisk(rows,market);
  const navRank=percentileRank(rows.map(r=>r.nav),rows.at(-1).nav);
  const currentDd=rollingDrawdowns(rows).at(-1);

  let index=
    internal.score*.48+
    marketScore*.22+
    (100-crashRisk)*.18+
    (100-navRank)*.07+
    clamp(-currentDd,0,35)*.14;

  index=clamp(index,0,100);

  let label="中立";
  let className="index-neutral";
  if(index>=78){label="かなり魅力的";className="index-excellent"}
  else if(index>=62){label="やや魅力的";className="index-good"}
  else if(index<38){label="警戒";className="index-risk"}

  return {
    index,label,className,
    internal:internal.score,
    market:marketScore,
    crashRisk,
    navRank,
    currentDd
  }
}

function buildMorningBrief(){
  if(!last.d)return;

  const market=getSavedMarketInputs();
  const action=calculateActionSignal(last.d,market);
  const idx=calculateWcmIndex(last.d,market);
  const outlook=calculateOutlook(
    last.d,
    market,
    +$("marketWeight").value||40,
    $("forecastCaution").value
  );
  const candidates=getLatestDistributionCandidates(last.d);
  const top=candidates[0];
  const latest=last.d.at(-1).nav;
  const oneMonth=recentReturn(last.d,21);

  const greeting=new Date().getHours()<12
    ?"おはようございます。"
    :new Date().getHours()<18
      ?"こんにちは。"
      :"こんばんは。";

  $("morningBrief").className="comment ai-hero";
  $("morningBrief").textContent=`${greeting}

現在の基準価額は${Math.round(latest).toLocaleString()}円です。直近1か月は${oneMonth>=0?"+":""}${oneMonth.toFixed(2)}%、WCM指数は${idx.index.toFixed(0)}点で「${idx.label}」です。

今日の参考判断は「${action.label}」です。来週中心予測は${Math.round(outlook.weekly.center).toLocaleString()}円、来月は${Math.round(outlook.monthly.center).toLocaleString()}円です。

次回分配金の最有力候補は${top?top.value.toLocaleString():"判定不能"}円です。`;

  $("dailyStatusCards").innerHTML=`
    <div class="card"><div class="card-title">今日の判断</div><div class="card-value">${action.label}</div><div class="card-sub">${action.score.toFixed(0)}/100</div></div>
    <div class="card"><div class="card-title">WCM指数</div><div class="card-value ${idx.className}">${idx.index.toFixed(0)}</div><div class="card-sub">${idx.label}</div></div>
    <div class="card"><div class="card-title">来週予測</div><div class="card-value">${Math.round(outlook.weekly.center).toLocaleString()}円</div><div class="card-sub">上昇確率 ${outlook.weekly.up.toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">暴落警戒度</div><div class="card-value">${action.crashRisk.toFixed(0)}</div><div class="card-sub">100に近いほど警戒</div></div>`;

  renderWcmIndex(idx);
  renderDistributionAi(candidates,idx,action);
  $("whatWouldIDo").disabled=false
}

function renderWcmIndex(idx){
  $("wcmIndexCards").innerHTML=`
    <div class="card"><div class="card-title">総合指数</div><div class="card-value ${idx.className}">${idx.index.toFixed(0)}/100</div><div class="card-sub">${idx.label}</div></div>
    <div class="card"><div class="card-title">内部スコア</div><div class="card-value">${idx.internal.toFixed(0)}</div></div>
    <div class="card"><div class="card-title">外部環境</div><div class="card-value">${idx.market.toFixed(0)}</div></div>
    <div class="card"><div class="card-title">価格の過去順位</div><div class="card-value">${idx.navRank.toFixed(1)}%</div></div>`;

  $("wcmIndexGauge").innerHTML=`
    <div class="scorebar"><span style="width:${idx.index}%"></span></div>
    <div class="small" style="margin-top:7px">警戒 0 ← WCM指数 → 100 魅力的</div>`
}

function renderDistributionAi(candidates,idx,action){
  if(!candidates.length){
    $("distributionAiCards").innerHTML='<div class="small">分配履歴がありません。</div>';
    $("distributionAiComment").textContent="予測に必要な分配履歴がありません。";
    return
  }

  $("distributionAiCards").innerHTML=candidates.map((c,index)=>`
    <div class="card">
      <div class="card-title">${index===0?"最有力候補":"候補 "+(index+1)}</div>
      <div class="card-value">${c.value.toLocaleString()}円</div>
      <div class="card-sub">${c.probability.toFixed(1)}%</div>
    </div>`).join("");

  const specialRisk=estimateSpecialDistributionRisk(last.d);
  $("distributionAiComment").textContent=`最有力候補は${candidates[0].value.toLocaleString()}円、参考確率は${candidates[0].probability.toFixed(1)}%です。

WCM指数は${idx.index.toFixed(0)}点、行動判定は「${action.label}」です。基準価額が過去レンジの下部にあるほど、個別元本によっては特別分配になりやすくなります。

特別分配リスクの参考推定は${specialRisk.toFixed(0)}%です。実際の普通分配・特別分配は各投資家の個別元本で決まります。`
}

function buildWhatWouldIDo(){
  if(!last.d)return;

  const market=getSavedMarketInputs();
  const action=calculateActionSignal(last.d,market);
  const idx=calculateWcmIndex(last.d,market);
  const oneMonth=recentReturn(last.d,21);
  const currentDd=rollingDrawdowns(last.d).at(-1);
  const reasons=[];

  if(idx.index>=68)reasons.push(`WCM指数が${idx.index.toFixed(0)}点で、過去データ上の魅力度が比較的高い`);
  if(idx.index<40)reasons.push(`WCM指数が${idx.index.toFixed(0)}点で、現時点のリスクが高い`);
  if(currentDd<=-10)reasons.push(`最高値から${Math.abs(currentDd).toFixed(1)}%下落している`);
  if(oneMonth<=-5)reasons.push(`直近1か月で${Math.abs(oneMonth).toFixed(1)}%下落している`);
  if(action.crashRisk>=65)reasons.push(`暴落警戒度が${action.crashRisk.toFixed(0)}点と高い`);
  if(action.crashRisk<40)reasons.push(`暴落警戒度が${action.crashRisk.toFixed(0)}点と比較的低い`);
  if(!reasons.length)reasons.push("強い買い材料と強い警戒材料が拮抗している");

  let decision="通常積立のみを継続します。";
  let second="追加投資は見送ります。";

  if(action.code==="buy"){
    decision="通常積立を継続します。";
    second="余裕資金がある場合は、追加資金を3〜5回に分けて投入します。"
  }else if(action.code==="take"){
    decision="新規の一括投資は控えます。";
    second="保有比率が大きすぎる場合だけ、一部利益確定や現金比率の調整を検討します。"
  }

  $("myDecision").innerHTML=`<strong>もし私なら</strong>

${decision}
${second}

<strong>理由</strong>
<ul class="decision-list">
${reasons.map(r=>`<li>${r}</li>`).join("")}
</ul>

生活防衛資金と事業資金は投資に回さず、判断を1回で決めずに分割します。`
}

function memoKey(){
  return `wcm10-memo-${new Date().toISOString().slice(0,10)}`
}

function saveDailyMemo(){
  localStorage.setItem(memoKey(),$("dailyMemo").value);
  $("memoStatus").className="status ok";
  $("memoStatus").textContent="今日のメモを保存しました。"
}

function clearDailyMemo(){
  $("dailyMemo").value="";
  localStorage.removeItem(memoKey());
  $("memoStatus").className="status";
  $("memoStatus").textContent="メモを消去しました。"
}

function restoreDailyMemo(){
  $("dailyMemo").value=localStorage.getItem(memoKey())||""
}

function getMarketInputs(){
  return {
    nasdaq:+$("nasdaqChange").value||0,
    sp:+$("spChange").value||0,
    usdJpy:+$("usdJpyChange").value||0,
    vix:+$("vixChange").value||0,
    growth:+$("growthIndexChange").value||0,
    yieldBp:+$("yieldChange").value||0
  }
}
function calculateMarketScore(data){
  let score=50;
  score+=clamp(data.nasdaq,-10,10)*2.2;
  score+=clamp(data.sp,-8,8)*1.3;
  score+=clamp(data.growth,-10,10)*2.5;
  score+=clamp(data.usdJpy,-6,6)*1.2;
  score-=clamp(data.vix,-30,50)*.45;
  score-=clamp(data.yieldBp,-50,80)*.18;
  return clamp(score,0,100)
}
function analyzeMarketEnvironment(){
  const d=getMarketInputs();
  const score=calculateMarketScore(d);
  const reasons=[];
  const positives=[];
  const cautions=[];

  if(d.nasdaq<=-2)reasons.push(`NASDAQ100が${d.nasdaq.toFixed(1)}%下落し、成長株全体に売り圧力がかかっています。`);
  if(d.nasdaq>=2)positives.push(`NASDAQ100が${d.nasdaq.toFixed(1)}%上昇し、成長株に追い風です。`);

  if(d.growth<=-2)reasons.push(`世界成長株指数が${d.growth.toFixed(1)}%下落し、WCMの投資対象に逆風です。`);
  if(d.growth>=2)positives.push(`世界成長株指数が${d.growth.toFixed(1)}%上昇し、WCMの投資対象に追い風です。`);

  if(d.usdJpy<=-1.5)reasons.push(`ドル円が${d.usdJpy.toFixed(1)}%円高方向へ動き、円換算の基準価額を押し下げやすい環境です。`);
  if(d.usdJpy>=1.5)positives.push(`ドル円が${d.usdJpy.toFixed(1)}%円安方向へ動き、円換算の基準価額を支えやすい環境です。`);

  if(d.vix>=15)reasons.push(`VIXが${d.vix.toFixed(1)}%上昇し、投資家のリスク回避姿勢が強まっています。`);
  if(d.vix<=-10)positives.push(`VIXが${d.vix.toFixed(1)}%低下し、市場心理が改善しています。`);

  if(d.yieldBp>=15)reasons.push(`米10年金利が${d.yieldBp.toFixed(0)}bp上昇し、高PER成長株の評価に逆風です。`);
  if(d.yieldBp<=-15)positives.push(`米10年金利が${Math.abs(d.yieldBp).toFixed(0)}bp低下し、成長株の評価に追い風です。`);

  if(d.sp<=-2)cautions.push(`S&P500も${d.sp.toFixed(1)}%下落しており、個別要因より市場全体の影響が強い可能性があります。`);
  if(d.sp>=2)positives.push(`S&P500が${d.sp.toFixed(1)}%上昇し、米国株全体の地合いが良好です。`);

  let tone="中立";
  let className="market-neutral";
  if(score>=65){tone="追い風";className="market-positive"}
  if(score<40){tone="逆風";className="market-negative"}

  const mainText=[
    `総合判定：${tone}（外部環境スコア ${score.toFixed(0)}/100）`,
    "",
    reasons.length ? "主な下落要因\n・"+reasons.join("\n・") : "明確な大きな下落要因は入力値から確認できません。",
    "",
    positives.length ? "主な上昇要因\n・"+positives.join("\n・") : "",
    cautions.length ? "\n補足\n・"+cautions.join("\n・") : "",
    "",
    "この分析は入力した市場データから機械的に作成した参考コメントです。"
  ].filter(Boolean).join("\n");

  $("marketAnalysis").className=`comment ${className}`;
  $("marketAnalysis").textContent=mainText;

  $("marketScoreCards").innerHTML=`
    <div class="card"><div class="card-title">外部環境スコア</div><div class="card-value">${score.toFixed(0)}/100</div><div class="card-sub">${tone}</div></div>
    <div class="card"><div class="card-title">成長株要因</div><div class="card-value">${(d.nasdaq+d.growth).toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">為替要因</div><div class="card-value">${d.usdJpy>=0?"+":""}${d.usdJpy.toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">リスク要因</div><div class="card-value">${d.vix.toFixed(1)}%</div><div class="card-sub">VIX変化</div></div>`;

  localStorage.setItem("wcm8-market",JSON.stringify(d))
}
function restoreMarketInputs(){
  try{
    const d=JSON.parse(localStorage.getItem("wcm8-market")||"null");
    if(!d)return;
    $("nasdaqChange").value=d.nasdaq??0;
    $("spChange").value=d.sp??0;
    $("usdJpyChange").value=d.usdJpy??0;
    $("vixChange").value=d.vix??0;
    $("growthIndexChange").value=d.growth??0;
    $("yieldChange").value=d.yieldBp??0
  }catch(_){}
}


function getSavedMarketInputs(){
  try{
    return JSON.parse(localStorage.getItem("wcm8-market")||"null")||{
      nasdaq:0,sp:0,usdJpy:0,vix:0,growth:0,yieldBp:0
    }
  }catch(_){
    return {nasdaq:0,sp:0,usdJpy:0,vix:0,growth:0,yieldBp:0}
  }
}

function calculateExternalReturnAdjustment(market,weightPercent){
  const raw=
    market.nasdaq*.24+
    market.sp*.10+
    market.growth*.32+
    market.usdJpy*.16-
    market.vix*.035-
    market.yieldBp*.012;

  return raw*(clamp(weightPercent,0,100)/100)
}

function calculateCrashRisk(rows,market){
  const oneMonth=recentReturn(rows,21);
  const quarter=recentReturn(rows,63);
  const currentDd=rollingDrawdowns(rows).at(-1);
  const volatility=vol(rows);

  let risk=25;
  risk+=clamp(-oneMonth,0,20)*1.5;
  risk+=clamp(-quarter,0,30)*.65;
  risk+=clamp(-currentDd,0,40)*.8;
  risk+=clamp(volatility-18,0,35)*.85;
  risk+=clamp(market.vix,0,60)*.45;
  risk+=clamp(-market.nasdaq,0,12)*1.2;
  risk+=clamp(market.yieldBp,0,80)*.12;

  return clamp(risk,0,100)
}

function calculateActionSignal(rows,market){
  const wcm=calculateWcmScore(rows);
  const marketScore=calculateMarketScore(market);
  const crashRisk=calculateCrashRisk(rows,market);
  const recent=recentReturn(rows,21);

  let score=
    wcm.score*.55+
    marketScore*.25+
    (100-crashRisk)*.20;

  if(recent>12)score-=10;
  if(recent<-12)score+=8;

  score=clamp(score,0,100);

  let label="様子見";
  let code="hold";
  let detail="通常積立を続け、追加投資は急がない判定です。";

  if(score>=68){
    label="積立・分割追加";
    code="buy";
    detail="過去データと外部環境の組み合わせでは、通常積立の継続と分割追加を検討できる判定です。";
  }else if(score<38){
    label="慎重・利益確定も検討";
    code="take";
    detail="短期的な下落または過熱のリスクが高く、新規の一括投資は慎重にする判定です。保有比率が大きすぎる場合は一部利益確定も選択肢です。";
  }

  return {score,label,code,detail,wcm,marketScore,crashRisk}
}

function calculateOutlook(rows,market,weight,caution){
  const weekly=forecast(rows,5);
  const monthly=forecast(rows,21);
  const adjustment=calculateExternalReturnAdjustment(market,weight);

  let cautionFactor=1;
  if(caution==="cautious")cautionFactor=.65;
  if(caution==="optimistic")cautionFactor=1.25;

  const latest=rows.at(-1).nav;
  const weeklyAdjusted=weekly.center*(1+adjustment/100*.25*cautionFactor);
  const monthlyAdjusted=monthly.center*(1+adjustment/100*cautionFactor);

  const weeklyReturn=(weeklyAdjusted/latest-1)*100;
  const monthlyReturn=(monthlyAdjusted/latest-1)*100;

  const weeklyUp=clamp(weekly.up+adjustment*2.2,5,95);
  const monthlyUp=clamp(monthly.up+adjustment*1.6,5,95);

  return {
    latest,
    weekly:{...weekly,center:weeklyAdjusted,returnRate:weeklyReturn,up:weeklyUp},
    monthly:{...monthly,center:monthlyAdjusted,returnRate:monthlyReturn,up:monthlyUp},
    adjustment
  }
}

function outlookLabel(returnRate){
  if(returnRate>=2)return {label:"上昇寄り",className:"outlook-up"};
  if(returnRate<=-2)return {label:"下落寄り",className:"outlook-down"};
  return {label:"横ばい",className:"outlook-flat"}
}

function renderOutlook(){
  if(!last.d)return;

  const market=getMarketInputs();
  const weight=+$("marketWeight").value||40;
  const caution=$("forecastCaution").value;
  const outlook=calculateOutlook(last.d,market,weight,caution);
  const weeklyLabel=outlookLabel(outlook.weekly.returnRate);
  const monthlyLabel=outlookLabel(outlook.monthly.returnRate);
  const action=calculateActionSignal(last.d,market);
  const risk=action.crashRisk;

  $("outlookCards").innerHTML=`
    <div class="card">
      <div class="card-title">現在基準価額</div>
      <div class="card-value">${Math.round(outlook.latest).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">来週中心予測</div>
      <div class="card-value">${Math.round(outlook.weekly.center).toLocaleString()}円</div>
      <div class="card-sub">${pct(outlook.weekly.returnRate)}・上昇確率 ${outlook.weekly.up.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">来月中心予測</div>
      <div class="card-value">${Math.round(outlook.monthly.center).toLocaleString()}円</div>
      <div class="card-sub">${pct(outlook.monthly.returnRate)}・上昇確率 ${outlook.monthly.up.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">外部環境補正</div>
      <div class="card-value">${pct(outlook.adjustment)}</div>
      <div class="card-sub">入力値による参考補正</div>
    </div>`;

  $("outlookReason").className=`comment ${monthlyLabel.className}`;
  $("outlookReason").textContent=`来週判定：${weeklyLabel.label}
来月判定：${monthlyLabel.label}

来週の中心予測は${Math.round(outlook.weekly.center).toLocaleString()}円、来月は${Math.round(outlook.monthly.center).toLocaleString()}円です。

この予測は、CSVの過去リターンを基礎に、市場環境入力を${weight}%反映しています。相場ニュースや運用会社の判断を直接取得した予測ではありません。`;

  $("actionSignal").innerHTML=`
    <span class="signal-pill signal-${action.code}">${action.label}</span>

${action.detail}

総合行動スコア：${action.score.toFixed(0)}/100`;

  $("actionScore").innerHTML=`
    <div class="scorebar"><span style="width:${action.score}%"></span></div>
    <div class="small" style="margin-top:7px">
      WCM内部スコア ${action.wcm.score.toFixed(0)}点・外部環境 ${action.marketScore.toFixed(0)}点・暴落警戒度 ${action.crashRisk.toFixed(0)}点
    </div>`;

  const riskClass=risk>=65?"risk-high":risk>=40?"risk-mid":"risk-low";
  const riskLabel=risk>=65?"高い":risk>=40?"中程度":"低い";

  $("crashRiskCards").innerHTML=`
    <div class="card">
      <div class="card-title">暴落警戒度</div>
      <div class="card-value">${risk.toFixed(0)}/100</div>
      <div class="card-sub">${riskLabel}</div>
    </div>
    <div class="card">
      <div class="card-title">1か月騰落率</div>
      <div class="card-value">${pct(recentReturn(last.d,21))}</div>
    </div>
    <div class="card">
      <div class="card-title">現在下落率</div>
      <div class="card-value">${rollingDrawdowns(last.d).at(-1).toFixed(2)}%</div>
    </div>
    <div class="card">
      <div class="card-title">年率変動率</div>
      <div class="card-value">${vol(last.d).toFixed(2)}%</div>
    </div>`;

  $("crashRiskComment").className=`comment ${riskClass}`;
  $("crashRiskComment").textContent=risk>=65
    ?"過去データと入力した市場環境では、急落への警戒度が高めです。一括投資より分割投資を優先し、生活防衛資金を確保してください。"
    :risk>=40
      ?"警戒度は中程度です。通常積立を基本とし、追加投資は複数回に分ける方が安全です。"
      :"急落警戒度は比較的低い状態です。ただし、突発的なニュースによる下落は予測できません。";

  localStorage.setItem("wcm9-outlook",JSON.stringify({weight,caution}))
}

function restoreOutlookSettings(){
  try{
    const saved=JSON.parse(localStorage.getItem("wcm9-outlook")||"null");
    if(!saved)return;
    $("marketWeight").value=saved.weight??40;
    $("forecastCaution").value=saved.caution??"normal"
  }catch(_){}
}

function createSnapshot(){
  if(!last.d||!last.rs)return null;
  const market=getSavedMarketInputs();
  const action=calculateActionSignal(last.d,market);
  const outlook=calculateOutlook(
    last.d,
    market,
    +$("marketWeight").value||40,
    $("forecastCaution").value
  );
  const best=[...last.rs].sort((a,b)=>b.value-a.value)[0];

  return {
    id:Date.now(),
    date:new Date().toLocaleString("ja-JP"),
    latestNav:last.d.at(-1).nav,
    bestMethod:best.name,
    bestValue:best.value,
    action:action.label,
    actionScore:action.score,
    crashRisk:action.crashRisk,
    weeklyForecast:outlook.weekly.center,
    monthlyForecast:outlook.monthly.center
  }
}

function loadHistory(){
  try{return JSON.parse(localStorage.getItem("wcm9-history")||"[]")}
  catch(_){return []}
}

function saveSnapshot(){
  const snapshot=createSnapshot();
  if(!snapshot)return;
  const history=loadHistory();
  history.unshift(snapshot);
  localStorage.setItem("wcm9-history",JSON.stringify(history.slice(0,20)));
  renderHistory()
}

function renderHistory(){
  const history=loadHistory();
  $("historyList").innerHTML=history.length
    ?history.map(item=>`
      <div class="history-item">
        <div class="history-head">
          <span>${item.date}</span>
          <span>${item.action}</span>
        </div>
        <div class="history-meta">
          基準価額：${Math.round(item.latestNav).toLocaleString()}円<br>
          最良方式：${item.bestMethod}（${yen(item.bestValue)}）<br>
          行動スコア：${item.actionScore.toFixed(0)}点・暴落警戒度：${item.crashRisk.toFixed(0)}点<br>
          来週予測：${Math.round(item.weeklyForecast).toLocaleString()}円・来月予測：${Math.round(item.monthlyForecast).toLocaleString()}円
        </div>
      </div>`).join("")
    :'<div class="small">保存された履歴はありません。</div>'
}

function clearHistory(){
  if(confirm("分析履歴をすべて削除しますか？")){
    localStorage.removeItem("wcm9-history");
    renderHistory()
  }
}


function getLatestDistributionCandidates(rows){
  const paid=rows.filter(r=>r.distribution>0).map(r=>r.distribution);
  if(!paid.length)return [];
  const recent=paid.slice(-36);
  const weighted=new Map();

  recent.forEach((value,index)=>{
    const recencyWeight=.5+(index+1)/recent.length;
    weighted.set(value,(weighted.get(value)||0)+recencyWeight)
  });

  const total=[...weighted.values()].reduce((s,v)=>s+v,0);
  return [...weighted.entries()]
    .map(([value,weight])=>({
      value:+value,
      probability:total?weight/total*100:0
    }))
    .sort((a,b)=>b.probability-a.probability)
    .slice(0,4)
}

function calculateWcmIndex(rows,market){
  const internal=calculateWcmScore(rows);
  const marketScore=calculateMarketScore(market);
  const crashRisk=calculateCrashRisk(rows,market);
  const navRank=percentileRank(rows.map(r=>r.nav),rows.at(-1).nav);
  const currentDd=rollingDrawdowns(rows).at(-1);

  let index=
    internal.score*.48+
    marketScore*.22+
    (100-crashRisk)*.18+
    (100-navRank)*.07+
    clamp(-currentDd,0,35)*.14;

  index=clamp(index,0,100);

  let label="中立";
  let className="index-neutral";
  if(index>=78){label="かなり魅力的";className="index-excellent"}
  else if(index>=62){label="やや魅力的";className="index-good"}
  else if(index<38){label="警戒";className="index-risk"}

  return {
    index,label,className,
    internal:internal.score,
    market:marketScore,
    crashRisk,
    navRank,
    currentDd
  }
}

function buildMorningBrief(){
  if(!last.d)return;

  const market=getSavedMarketInputs();
  const action=calculateActionSignal(last.d,market);
  const idx=calculateWcmIndex(last.d,market);
  const outlook=calculateOutlook(
    last.d,
    market,
    +$("marketWeight").value||40,
    $("forecastCaution").value
  );
  const candidates=getLatestDistributionCandidates(last.d);
  const top=candidates[0];
  const latest=last.d.at(-1).nav;
  const oneMonth=recentReturn(last.d,21);

  const greeting=new Date().getHours()<12
    ?"おはようございます。"
    :new Date().getHours()<18
      ?"こんにちは。"
      :"こんばんは。";

  $("morningBrief").className="comment ai-hero";
  $("morningBrief").textContent=`${greeting}

現在の基準価額は${Math.round(latest).toLocaleString()}円です。直近1か月は${oneMonth>=0?"+":""}${oneMonth.toFixed(2)}%、WCM指数は${idx.index.toFixed(0)}点で「${idx.label}」です。

今日の参考判断は「${action.label}」です。来週中心予測は${Math.round(outlook.weekly.center).toLocaleString()}円、来月は${Math.round(outlook.monthly.center).toLocaleString()}円です。

次回分配金の最有力候補は${top?top.value.toLocaleString():"判定不能"}円です。`;

  $("dailyStatusCards").innerHTML=`
    <div class="card"><div class="card-title">今日の判断</div><div class="card-value">${action.label}</div><div class="card-sub">${action.score.toFixed(0)}/100</div></div>
    <div class="card"><div class="card-title">WCM指数</div><div class="card-value ${idx.className}">${idx.index.toFixed(0)}</div><div class="card-sub">${idx.label}</div></div>
    <div class="card"><div class="card-title">来週予測</div><div class="card-value">${Math.round(outlook.weekly.center).toLocaleString()}円</div><div class="card-sub">上昇確率 ${outlook.weekly.up.toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">暴落警戒度</div><div class="card-value">${action.crashRisk.toFixed(0)}</div><div class="card-sub">100に近いほど警戒</div></div>`;

  renderWcmIndex(idx);
  renderDistributionAi(candidates,idx,action);
  $("whatWouldIDo").disabled=false
}

function renderWcmIndex(idx){
  $("wcmIndexCards").innerHTML=`
    <div class="card"><div class="card-title">総合指数</div><div class="card-value ${idx.className}">${idx.index.toFixed(0)}/100</div><div class="card-sub">${idx.label}</div></div>
    <div class="card"><div class="card-title">内部スコア</div><div class="card-value">${idx.internal.toFixed(0)}</div></div>
    <div class="card"><div class="card-title">外部環境</div><div class="card-value">${idx.market.toFixed(0)}</div></div>
    <div class="card"><div class="card-title">価格の過去順位</div><div class="card-value">${idx.navRank.toFixed(1)}%</div></div>`;

  $("wcmIndexGauge").innerHTML=`
    <div class="scorebar"><span style="width:${idx.index}%"></span></div>
    <div class="small" style="margin-top:7px">警戒 0 ← WCM指数 → 100 魅力的</div>`
}

function renderDistributionAi(candidates,idx,action){
  if(!candidates.length){
    $("distributionAiCards").innerHTML='<div class="small">分配履歴がありません。</div>';
    $("distributionAiComment").textContent="予測に必要な分配履歴がありません。";
    return
  }

  $("distributionAiCards").innerHTML=candidates.map((c,index)=>`
    <div class="card">
      <div class="card-title">${index===0?"最有力候補":"候補 "+(index+1)}</div>
      <div class="card-value">${c.value.toLocaleString()}円</div>
      <div class="card-sub">${c.probability.toFixed(1)}%</div>
    </div>`).join("");

  const specialRisk=estimateSpecialDistributionRisk(last.d);
  $("distributionAiComment").textContent=`最有力候補は${candidates[0].value.toLocaleString()}円、参考確率は${candidates[0].probability.toFixed(1)}%です。

WCM指数は${idx.index.toFixed(0)}点、行動判定は「${action.label}」です。基準価額が過去レンジの下部にあるほど、個別元本によっては特別分配になりやすくなります。

特別分配リスクの参考推定は${specialRisk.toFixed(0)}%です。実際の普通分配・特別分配は各投資家の個別元本で決まります。`
}

function buildWhatWouldIDo(){
  if(!last.d)return;

  const market=getSavedMarketInputs();
  const action=calculateActionSignal(last.d,market);
  const idx=calculateWcmIndex(last.d,market);
  const oneMonth=recentReturn(last.d,21);
  const currentDd=rollingDrawdowns(last.d).at(-1);
  const reasons=[];

  if(idx.index>=68)reasons.push(`WCM指数が${idx.index.toFixed(0)}点で、過去データ上の魅力度が比較的高い`);
  if(idx.index<40)reasons.push(`WCM指数が${idx.index.toFixed(0)}点で、現時点のリスクが高い`);
  if(currentDd<=-10)reasons.push(`最高値から${Math.abs(currentDd).toFixed(1)}%下落している`);
  if(oneMonth<=-5)reasons.push(`直近1か月で${Math.abs(oneMonth).toFixed(1)}%下落している`);
  if(action.crashRisk>=65)reasons.push(`暴落警戒度が${action.crashRisk.toFixed(0)}点と高い`);
  if(action.crashRisk<40)reasons.push(`暴落警戒度が${action.crashRisk.toFixed(0)}点と比較的低い`);
  if(!reasons.length)reasons.push("強い買い材料と強い警戒材料が拮抗している");

  let decision="通常積立のみを継続します。";
  let second="追加投資は見送ります。";

  if(action.code==="buy"){
    decision="通常積立を継続します。";
    second="余裕資金がある場合は、追加資金を3〜5回に分けて投入します。"
  }else if(action.code==="take"){
    decision="新規の一括投資は控えます。";
    second="保有比率が大きすぎる場合だけ、一部利益確定や現金比率の調整を検討します。"
  }

  $("myDecision").innerHTML=`<strong>もし私なら</strong>

${decision}
${second}

<strong>理由</strong>
<ul class="decision-list">
${reasons.map(r=>`<li>${r}</li>`).join("")}
</ul>

生活防衛資金と事業資金は投資に回さず、判断を1回で決めずに分割します。`
}

function memoKey(){
  return `wcm10-memo-${new Date().toISOString().slice(0,10)}`
}

function saveDailyMemo(){
  localStorage.setItem(memoKey(),$("dailyMemo").value);
  $("memoStatus").className="status ok";
  $("memoStatus").textContent="今日のメモを保存しました。"
}

function clearDailyMemo(){
  $("dailyMemo").value="";
  localStorage.removeItem(memoKey());
  $("memoStatus").className="status";
  $("memoStatus").textContent="メモを消去しました。"
}

function restoreDailyMemo(){
  $("dailyMemo").value=localStorage.getItem(memoKey())||""
}


/* =========================================================
   Ver.13 Walk-forward Forecast Validation
   ========================================================= */

const ForecastValidationEngine=(()=>{
  const MODEL_DEFINITIONS=[
    {id:"historical",label:"過去平均"},
    {id:"ewma",label:"EWMA"},
    {id:"momentum",label:"モメンタム"},
    {id:"mean-reversion",label:"平均回帰"},
    {id:"equal-ensemble",label:"均等アンサンブル"}
  ];

  function cleanLogReturns(rows){
    const values=[];
    for(let index=1;index<rows.length;index++){
      const previous=rows[index-1].nav;
      const current=rows[index].nav;
      if(previous>0&&current>0){
        values.push(Math.log(current/previous));
      }
    }
    return values;
  }

  function weightedMean(values,decay=.97){
    if(!values.length)return 0;
    let numerator=0;
    let denominator=0;
    let weight=1;
    for(let index=values.length-1;index>=0;index--){
      numerator+=values[index]*weight;
      denominator+=weight;
      weight*=decay;
    }
    return denominator?numerator/denominator:0;
  }

  function zForCoverage(coverage){
    if(coverage>=.949)return 1.96;
    if(coverage>=.899)return 1.645;
    return 1.282;
  }

  function modelDailyDrift(modelId,logReturns){
    const longMean=mean(logReturns);
    const recent21=logReturns.slice(-Math.min(21,logReturns.length));
    const recentMean=mean(recent21);

    if(modelId==="historical")return longMean;
    if(modelId==="ewma")return weightedMean(logReturns,.97);
    if(modelId==="momentum"){
      return longMean*.35+recentMean*.65;
    }
    if(modelId==="mean-reversion"){
      return longMean-(recentMean-longMean)*.45;
    }
    throw new Error(`未対応の予測モデルです: ${modelId}`);
  }

  function predictBase(modelId,trainingRows,horizon,coverage){
    const logs=cleanLogReturns(trainingRows);
    if(logs.length<20)throw new Error("予測に必要な履歴が不足しています。");

    const latest=trainingRows.at(-1).nav;
    const drift=modelDailyDrift(modelId,logs);
    const volatility=sd(logs);
    const center=latest*Math.exp(drift*horizon);
    const z=zForCoverage(coverage);
    const range=z*volatility*Math.sqrt(horizon);

    return {
      center,
      low:latest*Math.exp(drift*horizon-range),
      high:latest*Math.exp(drift*horizon+range),
      dailyDrift:drift,
      volatility
    };
  }

  function predictAll(trainingRows,horizon,coverage){
    const baseIds=["historical","ewma","momentum","mean-reversion"];
    const base=Object.fromEntries(
      baseIds.map(id=>[id,predictBase(id,trainingRows,horizon,coverage)])
    );

    const centers=baseIds.map(id=>base[id].center);
    const lows=baseIds.map(id=>base[id].low);
    const highs=baseIds.map(id=>base[id].high);

    base["equal-ensemble"]={
      center:mean(centers),
      low:mean(lows),
      high:mean(highs),
      dailyDrift:mean(baseIds.map(id=>base[id].dailyDrift)),
      volatility:mean(baseIds.map(id=>base[id].volatility))
    };

    return base;
  }

  function metricFromRecords(records,coverage){
    if(!records.length){
      return {
        count:0,mape:NaN,rmsePct:NaN,biasPct:NaN,
        directionHit:NaN,coverage:NaN,score:0
      };
    }

    const percentageErrors=records.map(record=>
      Math.abs(record.predicted-record.actual)/record.actual*100
    );
    const signedErrors=records.map(record=>
      (record.predicted-record.actual)/record.actual*100
    );
    const squaredErrors=records.map(record=>
      ((record.predicted-record.actual)/record.actual*100)**2
    );

    const directionHits=records.filter(record=>{
      const predictedDirection=Math.sign(record.predicted-record.origin);
      const actualDirection=Math.sign(record.actual-record.origin);
      return predictedDirection===actualDirection ||
        (predictedDirection===0&&actualDirection===0);
    }).length/records.length*100;

    const intervalCoverage=records.filter(record=>
      record.actual>=record.low&&record.actual<=record.high
    ).length/records.length*100;

    const mape=mean(percentageErrors);
    const rmsePct=Math.sqrt(mean(squaredErrors));
    const biasPct=mean(signedErrors);
    const targetCoverage=coverage*100;

    const errorComponent=clamp(100-mape*5,0,100);
    const directionComponent=clamp(directionHits,0,100);
    const coverageComponent=clamp(
      100-Math.abs(intervalCoverage-targetCoverage)*2.5,
      0,
      100
    );
    const biasComponent=clamp(100-Math.abs(biasPct)*6,0,100);

    const score=clamp(
      errorComponent*.45+
      directionComponent*.30+
      coverageComponent*.15+
      biasComponent*.10,
      0,
      100
    );

    return {
      count:records.length,
      mape,
      rmsePct,
      biasPct,
      directionHit:directionHits,
      coverage:intervalCoverage,
      score
    };
  }

  function run(rows,options={}){
    const horizon=Math.max(1,+options.horizon||21);
    const lookback=Math.max(40,+options.lookback||120);
    const step=Math.max(1,+options.step||5);
    const interval=clamp(+options.interval||.90,.5,.99);
    const minimumOrigin=Math.max(lookback,60);

    if(rows.length<minimumOrigin+horizon+1){
      throw new Error(
        `データ不足です。最低でも${minimumOrigin+horizon+1}営業日程度必要です。`
      );
    }

    const recordsByModel=Object.fromEntries(
      MODEL_DEFINITIONS.map(model=>[model.id,[]])
    );

    for(
      let originIndex=minimumOrigin-1;
      originIndex+horizon<rows.length;
      originIndex+=step
    ){
      const trainingStart=Math.max(0,originIndex-lookback+1);
      const trainingRows=rows.slice(trainingStart,originIndex+1);
      const origin=rows[originIndex].nav;
      const actual=rows[originIndex+horizon].nav;
      const predictions=predictAll(trainingRows,horizon,interval);

      for(const model of MODEL_DEFINITIONS){
        const prediction=predictions[model.id];
        recordsByModel[model.id].push({
          date:rows[originIndex].date,
          dateText:rows[originIndex].dateText,
          origin,
          actual,
          predicted:prediction.center,
          low:prediction.low,
          high:prediction.high
        });
      }
    }

    const models=MODEL_DEFINITIONS.map(model=>({
      ...model,
      records:recordsByModel[model.id],
      metrics:metricFromRecords(recordsByModel[model.id],interval)
    }));

    const eligible=models.filter(model=>
      Number.isFinite(model.metrics.rmsePct)&&model.metrics.count>0
    );

    const rawWeights=eligible.map(model=>
      1/Math.max(model.metrics.rmsePct,0.25)**2
    );
    const weightTotal=rawWeights.reduce((sum,value)=>sum+value,0)||1;

    const weights=Object.fromEntries(
      eligible.map((model,index)=>[
        model.id,
        rawWeights[index]/weightTotal
      ])
    );

    const latestTraining=rows.slice(-lookback);
    const latestPredictions=predictAll(latestTraining,horizon,interval);
    const weightedIds=["historical","ewma","momentum","mean-reversion","equal-ensemble"]
      .filter(id=>weights[id]>0);

    const weightedForecast={
      center:weightedIds.reduce(
        (sum,id)=>sum+latestPredictions[id].center*weights[id],
        0
      ),
      low:weightedIds.reduce(
        (sum,id)=>sum+latestPredictions[id].low*weights[id],
        0
      ),
      high:weightedIds.reduce(
        (sum,id)=>sum+latestPredictions[id].high*weights[id],
        0
      )
    };

    const weightedRecords=[];
    const referenceRecords=recordsByModel["historical"];

    for(let index=0;index<referenceRecords.length;index++){
      let predicted=0;
      let low=0;
      let high=0;

      for(const id of weightedIds){
        const record=recordsByModel[id][index];
        predicted+=record.predicted*weights[id];
        low+=record.low*weights[id];
        high+=record.high*weights[id];
      }

      weightedRecords.push({
        ...referenceRecords[index],
        predicted,
        low,
        high
      });
    }

    const weightedMetrics=metricFromRecords(weightedRecords,interval);
    const best=[...models].sort(
      (left,right)=>right.metrics.score-left.metrics.score
    )[0];

    return {
      horizon,
      lookback,
      step,
      interval,
      models,
      weights,
      weightedForecast,
      weightedMetrics,
      weightedRecords,
      best,
      validationCount:weightedRecords.length,
      latestNav:rows.at(-1).nav
    };
  }

  return Object.freeze({
    run,
    predictAll,
    metricFromRecords,
    definitions:()=>MODEL_DEFINITIONS.map(model=>({...model}))
  });
})();

function accuracyClass(score){
  if(score>=75)return "accuracy-high";
  if(score>=55)return "accuracy-mid";
  return "accuracy-low";
}

function runForecastValidation(){
  const status=$("backtestStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  status.className="status";
  status.textContent="未来データを分離して精度を検証しています…";

  setTimeout(()=>{
    try{
      const result=ForecastValidationEngine.run(last.d,{
        horizon:+$("btHorizon").value,
        lookback:+$("btLookback").value,
        step:+$("btStep").value,
        interval:+$("btInterval").value
      });

      last.validation=result;
      renderForecastValidation(result);

      status.className="status ok";
      status.textContent=`精度検証が完了しました。検証回数：${result.validationCount}回`;
    }catch(error){
      console.error(error);
      status.className="status bad";
      status.textContent=`精度検証エラー：${error.message}`;
    }
  },40);
}

function renderForecastValidation(result){
  const best=result.best;
  const weighted=result.weightedMetrics;
  const weightedReturn=(
    result.weightedForecast.center/result.latestNav-1
  )*100;

  $("backtestCards").innerHTML=`
    <div class="card">
      <div class="card-title">検証回数</div>
      <div class="card-value">${result.validationCount}</div>
      <div class="card-sub">ウォークフォワード</div>
    </div>
    <div class="card">
      <div class="card-title">最優秀モデル</div>
      <div class="card-value">${best.label}</div>
      <div class="card-sub">信頼度 ${best.metrics.score.toFixed(0)}点</div>
    </div>
    <div class="card">
      <div class="card-title">加重予測MAPE</div>
      <div class="card-value">${weighted.mape.toFixed(2)}%</div>
      <div class="card-sub">平均絶対誤差率</div>
    </div>
    <div class="card">
      <div class="card-title">加重方向的中率</div>
      <div class="card-value">${weighted.directionHit.toFixed(1)}%</div>
    </div>`;

  $("backtestTable").innerHTML=`
    <div class="tablewrap">
      <table>
        <thead>
          <tr>
            <th>モデル</th>
            <th>信頼度</th>
            <th>MAPE</th>
            <th>RMSE</th>
            <th>方向的中</th>
            <th>区間カバー</th>
            <th>偏り</th>
          </tr>
        </thead>
        <tbody>
          ${result.models.map(model=>`
            <tr>
              <td>${model.label}</td>
              <td class="${accuracyClass(model.metrics.score)}">${model.metrics.score.toFixed(0)}点</td>
              <td>${model.metrics.mape.toFixed(2)}%</td>
              <td>${model.metrics.rmsePct.toFixed(2)}%</td>
              <td>${model.metrics.directionHit.toFixed(1)}%</td>
              <td>${model.metrics.coverage.toFixed(1)}%</td>
              <td>${model.metrics.biasPct>=0?"+":""}${model.metrics.biasPct.toFixed(2)}%</td>
            </tr>`).join("")}
        </tbody>
      </table>
    </div>`;

  const sortedWeights=Object.entries(result.weights)
    .map(([id,weight])=>({
      id,
      weight,
      label:result.models.find(model=>model.id===id)?.label||id
    }))
    .sort((left,right)=>right.weight-left.weight);

  $("modelWeights").innerHTML=sortedWeights.map(item=>`
    <div class="weight-row">
      <span>${item.label}</span>
      <div class="weight-bar"><span style="width:${item.weight*100}%"></span></div>
      <strong>${(item.weight*100).toFixed(1)}%</strong>
    </div>`).join("");

  $("weightedForecastCards").innerHTML=`
    <div class="card">
      <div class="card-title">現在基準価額</div>
      <div class="card-value">${Math.round(result.latestNav).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">精度加重中心予測</div>
      <div class="card-value">${Math.round(result.weightedForecast.center).toLocaleString()}円</div>
      <div class="card-sub">${pct(weightedReturn)}</div>
    </div>
    <div class="card">
      <div class="card-title">予測下限</div>
      <div class="card-value">${Math.round(result.weightedForecast.low).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">予測上限</div>
      <div class="card-value">${Math.round(result.weightedForecast.high).toLocaleString()}円</div>
    </div>`;

  const intervalTarget=result.interval*100;
  const coverageDifference=weighted.coverage-intervalTarget;
  let coverageText;

  if(Math.abs(coverageDifference)<=7){
    coverageText="予測区間の広さは実績と概ね整合しています。";
  }else if(coverageDifference<0){
    coverageText="予測区間が狭すぎる傾向があり、想定外の値動きを過小評価しています。";
  }else{
    coverageText="予測区間が広めで、やや慎重な設定です。";
  }

  $("backtestComment").textContent=`検証結果

最優秀モデル：
${best.label}（信頼度 ${best.metrics.score.toFixed(0)}点）

精度加重モデル：
MAPE ${weighted.mape.toFixed(2)}%
RMSE ${weighted.rmsePct.toFixed(2)}%
方向的中率 ${weighted.directionHit.toFixed(1)}%
${Math.round(intervalTarget)}%区間カバー率 ${weighted.coverage.toFixed(1)}%
予測の平均的な偏り ${weighted.biasPct>=0?"+":""}${weighted.biasPct.toFixed(2)}%

${coverageText}

検証回数が少ない場合や、相場環境が大きく変わった場合は、信頼度が高くても将来の精度を保証しません。`;

  $("weightedForecastComment").className="comment validation-note";
  $("weightedForecastComment").textContent=`精度加重予測

${result.horizon}営業日後の中心予測は${Math.round(result.weightedForecast.center).toLocaleString()}円です。
過去の検証でRMSEが小さかったモデルほど、大きな重みを付けています。

最も大きい重み：
${sortedWeights[0].label} ${(sortedWeights[0].weight*100).toFixed(1)}%

単一モデルの予測ではなく、複数モデルの検証結果を統合した参考値です。`;

  const recent=result.weightedRecords.slice(-Math.min(60,result.weightedRecords.length));
  lineChart(
    $("backtestChart"),
    [
      {
        name:"実績",
        color:"#22c55e",
        values:recent.map(record=>record.actual)
      },
      {
        name:"精度加重予測",
        color:"#3b82f6",
        values:recent.map(record=>record.predicted)
      }
    ]
  );
}


/* =========================================================
   Ver.14 Market Regime & Similar Period Analysis
   ========================================================= */

const MarketRegimeEngine=(()=>{
  function windowSlice(rows,endIndex,window){
    const start=Math.max(0,endIndex-window+1);
    return rows.slice(start,endIndex+1);
  }

  function featureVector(rows){
    const navs=rows.map(row=>row.nav);
    const logs=[];
    for(let i=1;i<navs.length;i++){
      if(navs[i-1]>0&&navs[i]>0){
        logs.push(Math.log(navs[i]/navs[i-1]));
      }
    }

    const latest=navs.at(-1);
    const first=navs[0];
    const totalReturn=first>0 ? latest/first-1 : 0;
    const annualizedVol=sd(logs)*Math.sqrt(252);
    const shortMean=mean(logs.slice(-Math.min(21,logs.length)));
    const longMean=mean(logs);
    const momentum=shortMean-longMean;
    const ddSeries=[];
    let high=-Infinity;
    for(const nav of navs){
      high=Math.max(high,nav);
      ddSeries.push(high>0?nav/high-1:0);
    }
    const currentDrawdown=ddSeries.at(-1)||0;
    const maxDrawdown=Math.min(...ddSeries,0);
    const positiveRatio=logs.length
      ? logs.filter(value=>value>0).length/logs.length
      : 0;
    const acceleration=logs.length>=42
      ? mean(logs.slice(-21))-mean(logs.slice(-42,-21))
      : 0;

    return {
      totalReturn,
      annualizedVol,
      momentum,
      currentDrawdown,
      maxDrawdown,
      positiveRatio,
      acceleration,
      latest
    };
  }

  function classify(features){
    const returnScore=clamp(50+features.totalReturn*220,0,100);
    const momentumScore=clamp(50+features.momentum*18000,0,100);
    const drawdownScore=clamp(100+features.currentDrawdown*260,0,100);
    const breadthScore=clamp(features.positiveRatio*100,0,100);
    const volatilityPenalty=clamp((features.annualizedVol-.15)*180,0,35);

    const bullScore=clamp(
      returnScore*.35+
      momentumScore*.25+
      drawdownScore*.25+
      breadthScore*.15-
      volatilityPenalty,
      0,
      100
    );

    const bearScore=clamp(
      (100-returnScore)*.35+
      (100-momentumScore)*.25+
      (100-drawdownScore)*.25+
      (100-breadthScore)*.15+
      volatilityPenalty*.6,
      0,
      100
    );

    const volatileScore=clamp(
      features.annualizedVol*220+
      Math.abs(features.maxDrawdown)*110,
      0,
      100
    );

    const neutralScore=clamp(
      100-Math.abs(bullScore-bearScore)-volatileScore*.25,
      0,
      100
    );

    const scores={
      bull:bullScore,
      neutral:neutralScore,
      bear:bearScore,
      volatile:volatileScore
    };

    const ordered=Object.entries(scores).sort((a,b)=>b[1]-a[1]);
    const [regime,topScore]=ordered[0];
    const secondScore=ordered[1][1];
    const confidence=clamp(50+(topScore-secondScore)*1.4,50,98);

    return {
      regime,
      confidence,
      scores,
      bullScore,
      bearScore,
      volatileScore,
      neutralScore
    };
  }

  function distance(a,b){
    const scales={
      totalReturn:.20,
      annualizedVol:.15,
      momentum:.0015,
      currentDrawdown:.15,
      maxDrawdown:.25,
      positiveRatio:.20,
      acceleration:.0015
    };

    const keys=Object.keys(scales);
    const squared=keys.reduce((sum,key)=>{
      const normalized=(a[key]-b[key])/scales[key];
      return sum+normalized*normalized;
    },0);

    return Math.sqrt(squared/keys.length);
  }

  function similarityScore(distanceValue){
    return clamp(100-distanceValue*22,0,100);
  }

  function futureReturn(rows,originIndex,horizon){
    const endIndex=originIndex+horizon;
    if(endIndex>=rows.length)return null;
    const start=rows[originIndex].nav;
    const end=rows[endIndex].nav;
    return start>0?end/start-1:null;
  }

  function analyze(rows,options={}){
    const window=Math.max(21,+options.window||63);
    const horizon=Math.max(5,+options.horizon||21);
    const count=Math.max(3,+options.count||5);

    if(rows.length<window+horizon){
      throw new Error(`現在の局面設定には${window+horizon}営業日必要です。`);
    }

    const currentRows=rows.slice(-window);
    const currentFeatures=featureVector(currentRows);
    const classification=classify(currentFeatures);

    const candidates=[];
    const currentStart=rows.length-window;
    const minimumGap=Math.max(window,horizon);

    for(let endIndex=window-1;endIndex+horizon<rows.length;endIndex++){
      if(endIndex>currentStart-minimumGap)continue;

      const periodRows=windowSlice(rows,endIndex,window);
      const features=featureVector(periodRows);
      const dist=distance(currentFeatures,features);
      const future=futureReturn(rows,endIndex,horizon);
      if(future===null)continue;

      candidates.push({
        endIndex,
        date:rows[endIndex].date,
        dateText:rows[endIndex].dateText,
        features,
        distance:dist,
        similarity:similarityScore(dist),
        futureReturn:future,
        classification:classify(features)
      });
    }

    const similar=candidates
      .sort((a,b)=>a.distance-b.distance)
      .slice(0,count);

    const futureReturns=similar.map(item=>item.futureReturn);
    const positiveProbability=futureReturns.length
      ? futureReturns.filter(value=>value>0).length/futureReturns.length*100
      : 0;

    return {
      window,
      horizon,
      count,
      currentFeatures,
      classification,
      similar,
      summary:{
        averageFutureReturn:mean(futureReturns),
        medianFutureReturn:median(futureReturns),
        minFutureReturn:Math.min(...futureReturns),
        maxFutureReturn:Math.max(...futureReturns),
        positiveProbability
      }
    };
  }

  function modelRecommendation(regime){
    const map={
      bull:{
        primary:"移動ブロック法",
        secondary:"定常ブートストラップ",
        reason:"上昇トレンドの連続性を残すモデルが局面を再現しやすいためです。"
      },
      neutral:{
        primary:"定常ブートストラップ",
        secondary:"混合モデル",
        reason:"トレンドと単日変動の両方をバランスよく扱えるためです。"
      },
      bear:{
        primary:"ランダム長ブロック",
        secondary:"混合モデル",
        reason:"下落局面の長さが一定でないため、可変長の連続性を残す方が現実的です。"
      },
      volatile:{
        primary:"t分布",
        secondary:"混合モデル",
        reason:"裾の厚い急変動を正規分布より表現しやすいためです。"
      }
    };
    return map[regime]||map.neutral;
  }

  return Object.freeze({
    analyze,
    featureVector,
    classify,
    modelRecommendation
  });
})();

function regimeLabel(regime){
  return {
    bull:"強気相場",
    neutral:"中立・持ち合い",
    bear:"弱気相場",
    volatile:"高ボラティリティ"
  }[regime]||regime;
}

function regimeClass(regime){
  return {
    bull:"regime-bull",
    neutral:"regime-neutral",
    bear:"regime-bear",
    volatile:"regime-volatile"
  }[regime]||"";
}

function runRegimeAnalysis(){
  const status=$("regimeStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  status.className="status";
  status.textContent="現在局面と過去の類似局面を分析しています…";

  setTimeout(()=>{
    try{
      const result=MarketRegimeEngine.analyze(last.d,{
        window:+$("regimeWindow").value,
        horizon:+$("similarHorizon").value,
        count:+$("similarCount").value
      });

      last.regime=result;
      renderRegimeAnalysis(result);

      status.className="status ok";
      status.textContent="相場局面の分析が完了しました。";
    }catch(error){
      console.error(error);
      status.className="status bad";
      status.textContent=`相場局面分析エラー：${error.message}`;
      $("regimeCards").innerHTML="";
      $("regimeGauge").innerHTML="";
      $("regimeComment").textContent="分析を完了できませんでした。設定とCSVデータを確認してください。";
      $("regimeModelCards").innerHTML="";
      $("regimeModelComment").textContent="";
      $("similarPeriodsTable").innerHTML="";
      $("similarSummaryCards").innerHTML="";
      $("similarComment").textContent="";
      $("similarChart").innerHTML="";
    }
  },40);
}

function renderRegimeAnalysis(result){
  const current=result.currentFeatures;
  const classification=result.classification;
  const label=regimeLabel(classification.regime);
  const recommendation=MarketRegimeEngine.modelRecommendation(
    classification.regime
  );

  $("regimeCards").innerHTML=`
    <div class="card">
      <div class="card-title">現在の局面</div>
      <div class="card-value ${regimeClass(classification.regime)}">${label}</div>
      <div class="card-sub">信頼度 ${classification.confidence.toFixed(0)}%</div>
    </div>
    <div class="card">
      <div class="card-title">期間リターン</div>
      <div class="card-value">${pct(current.totalReturn*100)}</div>
    </div>
    <div class="card">
      <div class="card-title">年率ボラティリティ</div>
      <div class="card-value">${(current.annualizedVol*100).toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">現在ドローダウン</div>
      <div class="card-value">${(current.currentDrawdown*100).toFixed(1)}%</div>
    </div>`;

  $("regimeGauge").innerHTML=`
    <div class="scorebar">
      <span style="width:${classification.confidence}%"></span>
    </div>
    <div class="small" style="margin-top:7px">
      強気 ${classification.bullScore.toFixed(0)}点・
      中立 ${classification.neutralScore.toFixed(0)}点・
      弱気 ${classification.bearScore.toFixed(0)}点・
      高ボラ ${classification.volatileScore.toFixed(0)}点
    </div>`;

  const regimeAdvice={
    bull:"上昇基調ですが、急上昇後は反落もあるため、追加投資は分割が安全です。",
    neutral:"方向感が弱いため、通常積立を中心にし、強いシグナルが出るまで一括投資は慎重にします。",
    bear:"下落基調です。元本割れリスクを重視し、生活防衛資金を確保した上で分割投資を検討します。",
    volatile:"値動きが大きい局面です。予測幅を広めに見て、単一モデルの結果に依存しないことが重要です。"
  }[classification.regime];

  $("regimeComment").innerHTML=`
    <span class="regime-pill ${classification.regime}">${label}</span>

判定期間：${result.window}営業日
上昇日比率：${(current.positiveRatio*100).toFixed(1)}%
最大ドローダウン：${(current.maxDrawdown*100).toFixed(1)}%
短期モメンタム：${(current.momentum*100).toFixed(3)}%

${regimeAdvice}`;

  $("regimeModelCards").innerHTML=`
    <div class="card">
      <div class="card-title">推奨モデル</div>
      <div class="card-value">${recommendation.primary}</div>
    </div>
    <div class="card">
      <div class="card-title">補助モデル</div>
      <div class="card-value">${recommendation.secondary}</div>
    </div>`;

  $("regimeModelComment").textContent=`${recommendation.reason}

Ver.13の精度検証結果がある場合は、局面推奨だけでなく、バックテストで信頼度が高いモデルも併せて確認してください。`;

  $("similarPeriodsTable").innerHTML=`
    <div class="tablewrap">
      <table>
        <thead>
          <tr>
            <th>順位</th>
            <th>基準日</th>
            <th>類似度</th>
            <th>当時の局面</th>
            <th>${result.horizon}日後</th>
          </tr>
        </thead>
        <tbody>
          ${result.similar.map((item,index)=>{
            const simClass=item.similarity>=75
              ?"similarity-high"
              :item.similarity>=55
                ?"similarity-mid"
                :"similarity-low";

            return `<tr>
              <td>${index+1}</td>
              <td>${item.dateText}</td>
              <td class="${simClass}">${item.similarity.toFixed(1)}%</td>
              <td>${regimeLabel(item.classification.regime)}</td>
              <td>${pct(item.futureReturn*100)}</td>
            </tr>`;
          }).join("")}
        </tbody>
      </table>
    </div>`;

  const summary=result.summary;

  $("similarSummaryCards").innerHTML=`
    <div class="card">
      <div class="card-title">平均リターン</div>
      <div class="card-value">${pct(summary.averageFutureReturn*100)}</div>
    </div>
    <div class="card">
      <div class="card-title">中央値</div>
      <div class="card-value">${pct(summary.medianFutureReturn*100)}</div>
    </div>
    <div class="card">
      <div class="card-title">上昇確率</div>
      <div class="card-value">${summary.positiveProbability.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">結果範囲</div>
      <div class="card-value">${pct(summary.minFutureReturn*100)}〜${pct(summary.maxFutureReturn*100)}</div>
    </div>`;

  let similarityInterpretation;
  const topSimilarity=result.similar[0]?.similarity||0;

  if(topSimilarity>=80){
    similarityInterpretation="現在と非常に近い過去局面が見つかりました。";
  }else if(topSimilarity>=60){
    similarityInterpretation="ある程度似た局面はありますが、完全一致ではありません。";
  }else{
    similarityInterpretation="過去に近い局面が少なく、類似局面分析の不確実性が高めです。";
  }

  $("similarComment").textContent=`過去の類似局面分析

最も似ている局面：
${result.similar[0]?.dateText||"該当なし"}
類似度 ${topSimilarity.toFixed(1)}%

${result.horizon}営業日後の平均：
${pct(summary.averageFutureReturn*100)}

上昇した割合：
${summary.positiveProbability.toFixed(1)}%

${similarityInterpretation}

類似局面は将来の再現を保証しません。金融政策、為替、銘柄構成などが異なる可能性があります。`;

  lineChart(
    $("similarChart"),
    [
      {
        name:"類似度",
        color:"#a855f7",
        values:result.similar.map(item=>item.similarity)
      },
      {
        name:"将来リターン（%）",
        color:"#22c55e",
        values:result.similar.map(item=>item.futureReturn*100)
      }
    ]
  );
}


/* =========================================================
   Ver.15 Integrated Investment Advisor
   ========================================================= */

const IntegratedAdvisorEngine=(()=>{
  function scoreRegime(regimeResult){
    const c=regimeResult.classification;
    const map={
      bull:82,
      neutral:62,
      bear:35,
      volatile:45
    };

    let score=map[c.regime]??55;

    if(c.regime==="bull"){
      score+=clamp((c.confidence-60)*.18,0,7);
    }
    if(c.regime==="bear"){
      score-=clamp((c.confidence-60)*.15,0,7);
    }
    if(c.regime==="volatile"){
      score-=clamp((c.volatileScore-60)*.12,0,8);
    }

    return clamp(score,0,100);
  }

  function scoreValidation(validationResult){
    if(!validationResult)return 50;

    const weighted=validationResult.weightedMetrics;
    const best=validationResult.best?.metrics?.score||50;
    const direction=weighted.directionHit||0;
    const errorScore=clamp(100-(weighted.mape||20)*5,0,100);

    return clamp(
      best*.35+
      direction*.30+
      errorScore*.35,
      0,
      100
    );
  }

  function scoreMonteCarlo(monteResult,riskTolerance){
    const summary=monteResult.summary;
    const loss=summary.lossProbability;
    const drawdown=Math.abs(summary.medianMaxDrawdown);
    const returnScore=clamp(50+summary.expectedMedianReturn*.65,0,100);

    const riskPenaltyByTolerance={
      low:1.25,
      medium:1,
      high:.75
    }[riskTolerance]||1;

    const lossScore=clamp(100-loss*riskPenaltyByTolerance,0,100);
    const ddScore=clamp(100-drawdown*1.5*riskPenaltyByTolerance,0,100);

    return clamp(
      returnScore*.40+
      lossScore*.35+
      ddScore*.25,
      0,
      100
    );
  }

  function scoreDrawdown(rows,riskTolerance){
    const current=Math.abs((()=>{
      let high=-Infinity;
      let latest=0;
      for(const row of rows){
        high=Math.max(high,row.nav);
        latest=high>0?row.nav/high-1:0;
      }
      return latest*100;
    })());

    const toleranceFactor={
      low:1.35,
      medium:1,
      high:.75
    }[riskTolerance]||1;

    return clamp(100-current*4*toleranceFactor,0,100);
  }

  function scoreVolatility(rows,riskTolerance){
    const annualVol=vol(rows);
    const acceptable={
      low:18,
      medium:25,
      high:35
    }[riskTolerance]||25;

    return clamp(100-Math.max(0,annualVol-acceptable)*3.3,15,100);
  }

  function scoreSimilarity(regimeResult){
    const summary=regimeResult.summary;
    const topSimilarity=regimeResult.similar[0]?.similarity||0;
    const positive=summary.positiveProbability;
    const futureScore=clamp(50+summary.averageFutureReturn*230,0,100);

    return clamp(
      topSimilarity*.35+
      positive*.35+
      futureScore*.30,
      0,
      100
    );
  }

  function actionFromScore(score,riskTolerance,regime){
    let adjusted=score;

    if(riskTolerance==="low")adjusted-=5;
    if(riskTolerance==="high")adjusted+=4;
    if(regime==="volatile")adjusted-=5;
    if(regime==="bear")adjusted-=8;

    if(adjusted>=88){
      return {
        label:"積極買い候補",
        className:"advisor-action-strong",
        message:"積立を継続し、追加投資は複数回に分けて検討できる水準です。"
      };
    }
    if(adjusted>=74){
      return {
        label:"積立継続",
        className:"advisor-action-buy",
        message:"通常積立の継続を中心にし、一括投資は分割する判断が適しています。"
      };
    }
    if(adjusted>=58){
      return {
        label:"様子を見ながら積立",
        className:"advisor-action-hold",
        message:"方向感が十分ではないため、通常積立を維持し、大きな追加投資は急がない判断です。"
      };
    }
    if(adjusted>=40){
      return {
        label:"慎重運用",
        className:"advisor-action-cautious",
        message:"下落や高ボラティリティへの備えを優先し、追加投資は少額・分割が適しています。"
      };
    }

    return {
      label:"リスク警戒",
      className:"advisor-action-risk",
      message:"元本割れや急落の可能性を重視し、新規投資より資金管理を優先する局面です。"
    };
  }

  function grade(score){
    if(score>=90)return "S";
    if(score>=80)return "A";
    if(score>=70)return "B";
    if(score>=60)return "C";
    if(score>=45)return "D";
    return "E";
  }

  function confidence(validationResult,regimeResult,monteResult){
    const validationScore=validationResult
      ?validationResult.weightedMetrics.directionHit
      :50;

    const regimeConfidence=regimeResult.classification.confidence;
    const modelSpread=monteResult.modelSpread??25;
    const monteConfidence=clamp(100-modelSpread*1.3,25,95);

    return clamp(
      validationScore*.40+
      regimeConfidence*.35+
      monteConfidence*.25,
      0,
      100
    );
  }

  function combine({
    rows,
    regimeResult,
    validationResult,
    monteResult,
    riskTolerance
  }){
    const components={
      regime:scoreRegime(regimeResult),
      validation:scoreValidation(validationResult),
      monteCarlo:scoreMonteCarlo(monteResult,riskTolerance),
      drawdown:scoreDrawdown(rows,riskTolerance),
      volatility:scoreVolatility(rows,riskTolerance),
      similarity:scoreSimilarity(regimeResult)
    };

    const weights={
      regime:.25,
      validation:.25,
      monteCarlo:.20,
      drawdown:.10,
      volatility:.10,
      similarity:.10
    };

    const total=Object.entries(weights).reduce(
      (sum,[key,weight])=>sum+components[key]*weight,
      0
    );

    const finalScore=clamp(total,0,100);
    const action=actionFromScore(
      finalScore,
      riskTolerance,
      regimeResult.classification.regime
    );

    return {
      score:finalScore,
      grade:grade(finalScore),
      action,
      confidence:confidence(
        validationResult,
        regimeResult,
        monteResult
      ),
      components,
      weights
    };
  }

  return Object.freeze({
    combine,
    grade,
    actionFromScore
  });
})();

function buildAdvisorMonte(horizon,runs){
  const days=Math.max(21,horizon);
  const years=Math.max(1,Math.ceil(days/252));

  const methods=[
    "iid",
    "moving-block",
    "stationary",
    "random-block",
    "hybrid"
  ];

  const results=methods.map(method=>
    MonteCarloEngine.simulate(
      returns(last.d),
      {
        ...getMonteConfig(method),
        years,
        runs,
        monthlyContribution:+$("monthly").value||0,
        captureYearly:false
      },
      getMonteSettings()
    )
  );

  const medianValues=results.map(result=>result.summary.median);
  const medianAverage=mean(medianValues);
  const medianMin=Math.min(...medianValues);
  const medianMax=Math.max(...medianValues);
  const spread=medianAverage>0
    ?(medianMax-medianMin)/medianAverage*100
    :0;

  let learnedWeights=LearningSystem.getModelWeights();

  try{
    const regime=last.regime?.classification?.regime
      ||last.advisor?.regimeResult?.classification?.regime
      ||"unknown";
    const horizon=+$("advisorHorizon")?.value||21;
    const adaptiveWeights=AdaptiveAIEngine.effectiveWeights(regime,horizon);

    if(adaptiveWeights){
      learnedWeights=adaptiveWeights;
    }
  }catch(error){
    console.warn("Adaptive AI重みの取得に失敗しました。",error);
  }

  function weightedMetric(selector){
    if(!learnedWeights){
      return mean(results.map(selector));
    }

    let numerator=0;
    let denominator=0;

    for(const result of results){
      const weight=learnedWeights[result.config.method]||0;
      numerator+=selector(result)*weight;
      denominator+=weight;
    }

    return denominator
      ?numerator/denominator
      :mean(results.map(selector));
  }

  const averageSummary={
    p05:weightedMetric(result=>result.summary.p05),
    median:weightedMetric(result=>result.summary.median),
    p95:weightedMetric(result=>result.summary.p95),
    lossProbability:weightedMetric(result=>result.summary.lossProbability),
    medianMaxDrawdown:weightedMetric(result=>result.summary.medianMaxDrawdown),
    expectedMedianReturn:weightedMetric(result=>result.summary.expectedMedianReturn)
  };

  return {
    results,
    summary:averageSummary,
    modelSpread:spread
  };
}

function ensureAdvisorValidation(horizon){
  const settings=DataAdaptiveMode.bestValidationSettings(
    last.d.length,
    {
      horizon,
      lookback:horizon<=21?120:252,
      step:horizon<=21?5:10
    }
  );

  return ForecastValidationEngine.run(last.d,{
    horizon:settings.horizon,
    lookback:settings.lookback,
    step:settings.step,
    interval:.90
  });
}

function ensureAdvisorRegime(horizon){
  const settings=DataAdaptiveMode.bestAdvisorSettings(
    last.d.length,
    horizon
  );
  const window=Math.min(
    settings.lookback,
    Math.max(21,last.d.length-settings.horizon-1)
  );

  return MarketRegimeEngine.analyze(last.d,{
    window:Math.max(21,window),
    horizon:Math.max(1,settings.horizon),
    count:Math.min(5,Math.max(3,Math.floor(last.d.length/30)))
  });
}

function runIntegratedAdvisor(){
  const status=$("advisorStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  status.className="status";
  status.textContent="相場局面・精度検証・モンテカルロを統合しています…";

  setTimeout(()=>{
    try{
      const horizon=+$("advisorHorizon").value||21;
      const riskTolerance=$("advisorRisk").value;
      const runs=+$("advisorRuns").value||1000;

      const regimeResult=ensureAdvisorRegime(horizon);
      const validationResult=ensureAdvisorValidation(horizon);
      const monteResult=buildAdvisorMonte(horizon,runs);

      const advisor=IntegratedAdvisorEngine.combine({
        rows:last.d,
        regimeResult,
        validationResult,
        monteResult,
        riskTolerance
      });

      const result={
        horizon,
        riskTolerance,
        runs,
        regimeResult,
        validationResult,
        monteResult,
        advisor
      };

      last.advisor=result;
      renderIntegratedAdvisor(result);

      status.className="status ok";
      status.textContent="総合判断が完了しました。";
    }catch(error){
      console.error(error);
      status.className="status bad";
      status.textContent=`総合判断エラー：${error.message}`;
    }
  },60);
}

function renderIntegratedAdvisor(result){
  const {advisor,regimeResult,validationResult,monteResult}=result;
  const summary=monteResult.summary;
  const regime=regimeLabel(regimeResult.classification.regime);
  const latest=last.d.at(-1).nav;
  const forecastReturn=latest>0
    ?(summary.median/latest-1)*100
    :0;

  $("advisorHero").innerHTML=`
    <div class="advisor-score">${advisor.score.toFixed(0)}点</div>
    <div class="advisor-grade">総合ランク ${advisor.grade}</div>
    <div class="small" style="margin-top:8px">
      判断信頼度 ${advisor.confidence.toFixed(0)}%
    </div>
    <span class="advisor-action-pill ${advisor.action.className}">
      ${advisor.action.label}
    </span>`;

  $("advisorScoreBar").innerHTML=`
    <div class="scorebar">
      <span style="width:${advisor.score}%"></span>
    </div>`;

  $("advisorAction").textContent=`AI総合判断

${advisor.action.message}

現在の相場局面：
${regime}
信頼度 ${regimeResult.classification.confidence.toFixed(0)}%

予測精度：
方向的中率 ${validationResult.weightedMetrics.directionHit.toFixed(1)}%
MAPE ${validationResult.weightedMetrics.mape.toFixed(2)}%

この判定は投資助言ではなく、読み込んだ過去データに基づく参考情報です。`;

  $("advisorForecastCards").innerHTML=`
    <div class="card">
      <div class="card-title">現在基準価額</div>
      <div class="card-value">${Math.round(latest).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">統合中心予測</div>
      <div class="card-value">${Math.round(summary.median).toLocaleString()}円</div>
      <div class="card-sub">${pct(forecastReturn)}</div>
    </div>
    <div class="card">
      <div class="card-title">慎重ケース</div>
      <div class="card-value">${Math.round(summary.p05).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">楽観ケース</div>
      <div class="card-value">${Math.round(summary.p95).toLocaleString()}円</div>
    </div>`;

  $("advisorForecastComment").textContent=`統合予測

予測期間：${result.horizon}営業日
使用モデル：5手法
試行回数：各${result.runs.toLocaleString()}回
モデル間中央値差：${monteResult.modelSpread.toFixed(1)}%

元本割れ確率：
${summary.lossProbability.toFixed(1)}%

モデル間の差が大きいほど、予測への依存は控えめにしてください。`;

  const labels={
    regime:"相場局面",
    validation:"予測精度",
    monteCarlo:"モンテカルロ",
    drawdown:"ドローダウン",
    volatility:"ボラティリティ",
    similarity:"類似局面"
  };

  $("advisorComponents").innerHTML=Object.entries(advisor.components)
    .map(([key,value])=>`
      <div class="advisor-component">
        <span>${labels[key]}</span>
        <div class="advisor-component-bar">
          <span style="width:${value}%"></span>
        </div>
        <strong>${value.toFixed(0)}点</strong>
      </div>`)
    .join("");

  const bestModel=validationResult.best;
  const topSimilar=regimeResult.similar[0];

  $("advisorEvidence").textContent=`判断根拠

相場局面：
${regime}

バックテスト最優秀モデル：
${bestModel.label}
信頼度 ${bestModel.metrics.score.toFixed(0)}点

最も似た過去局面：
${topSimilar?.dateText||"該当なし"}
類似度 ${topSimilar?.similarity.toFixed(1)||"0.0"}%

類似局面後の上昇割合：
${regimeResult.summary.positiveProbability.toFixed(1)}%

これらの根拠が同じ方向を示すほど、総合判断の信頼度が高くなります。`;

  $("advisorModelTable").innerHTML=`
    <div class="tablewrap">
      <table>
        <thead>
          <tr>
            <th>モデル</th>
            <th>中央値</th>
            <th>下位5%</th>
            <th>上位5%</th>
            <th>元本割れ</th>
          </tr>
        </thead>
        <tbody>
          ${monteResult.results.map(item=>`
            <tr>
              <td>${MonteCarloEngine.methodLabel(item.config)}</td>
              <td>${yen(item.summary.median)}</td>
              <td>${yen(item.summary.p05)}</td>
              <td>${yen(item.summary.p95)}</td>
              <td>${item.summary.lossProbability.toFixed(1)}%</td>
            </tr>`).join("")}
        </tbody>
      </table>
    </div>`;

  $("advisorModelComment").textContent=`モデル統合

5手法の中央値を平均して、単一モデルへの依存を抑えています。

モデル間中央値差：
${monteResult.modelSpread.toFixed(1)}%

差が15%未満なら比較的安定、35%以上ならモデル依存性が高いと考えます。`;

  const annualVol=vol(last.d);
  const currentDd=(()=>{
    let high=-Infinity;
    let dd=0;
    for(const row of last.d){
      high=Math.max(high,row.nav);
      dd=high>0?row.nav/high-1:0;
    }
    return dd*100;
  })();

  $("advisorRiskCards").innerHTML=`
    <div class="card">
      <div class="card-title">元本割れ確率</div>
      <div class="card-value">${summary.lossProbability.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">最大DD中央値</div>
      <div class="card-value">${summary.medianMaxDrawdown.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">現在DD</div>
      <div class="card-value">${currentDd.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">年率ボラティリティ</div>
      <div class="card-value">${annualVol.toFixed(1)}%</div>
    </div>`;

  let riskText;
  if(summary.lossProbability<20&&Math.abs(summary.medianMaxDrawdown)<25){
    riskText="総合リスクは比較的低めです。ただし、急変時には過去より大きく下落する可能性があります。";
  }else if(summary.lossProbability<40&&Math.abs(summary.medianMaxDrawdown)<40){
    riskText="総合リスクは中程度です。通常積立を中心にし、追加投資は分割する方が安全です。";
  }else{
    riskText="総合リスクは高めです。元本割れと大幅下落を想定し、無理な追加投資は避ける判断が適しています。";
  }

  $("advisorRiskComment").textContent=riskText;
}


/* =========================================================
   Ver.16 Persistent Learning System
   ========================================================= */

const LearningSystem=(()=>{
  const STORAGE_KEY="wcm16-learning-v1";
  const MAX_PREDICTIONS=100;

  function loadState(){
    try{
      const parsed=JSON.parse(localStorage.getItem(STORAGE_KEY)||"null");
      if(parsed&&Array.isArray(parsed.predictions)){
        return parsed;
      }
    }catch(error){
      console.warn("学習データの読込に失敗しました。",error);
    }

    return {
      version:1,
      predictions:[],
      modelStats:{}
    };
  }

  function saveState(state){
    localStorage.setItem(
      STORAGE_KEY,
      JSON.stringify({
        ...state,
        predictions:state.predictions.slice(0,MAX_PREDICTIONS)
      })
    );
  }

  function clear(){
    localStorage.removeItem(STORAGE_KEY);
  }

  function createPrediction(advisorResult,rows){
    if(!advisorResult)throw new Error("先に総合判断を実行してください。");

    const latestRow=rows.at(-1);
    const targetIndex=Math.min(
      rows.length-1,
      rows.length-1+advisorResult.horizon
    );

    const modelPredictions=advisorResult.monteResult.results.map(item=>({
      id:item.config.method,
      label:MonteCarloEngine.methodLabel(item.config),
      predicted:item.summary.median,
      p05:item.summary.p05,
      p95:item.summary.p95
    }));

    return {
      id:`prediction-${Date.now()}-${Math.random().toString(36).slice(2,8)}`,
      createdAt:new Date().toISOString(),
      originDate:latestRow.dateText,
      originDateValue:latestRow.date instanceof Date
        ?latestRow.date.toISOString()
        :latestRow.date,
      originNav:latestRow.nav,
      horizon:advisorResult.horizon,
      targetDate:null,
      advisorScore:advisorResult.advisor.score,
      advisorGrade:advisorResult.advisor.grade,
      advisorAction:advisorResult.advisor.action.label,
      confidence:advisorResult.advisor.confidence,
      regime:advisorResult.regimeResult.classification.regime,
      integratedPrediction:advisorResult.monteResult.summary.median,
      integratedLow:advisorResult.monteResult.summary.p05,
      integratedHigh:advisorResult.monteResult.summary.p95,
      modelPredictions,
      evaluated:false,
      actualNav:null,
      actualDate:null,
      integratedErrorPct:null,
      directionCorrect:null
    };
  }

  function findOriginIndex(rows,prediction){
    return rows.findIndex(row=>{
      if(row.dateText===prediction.originDate)return true;
      const dateValue=row.date instanceof Date
        ?row.date.toISOString()
        :String(row.date||"");
      return dateValue===prediction.originDateValue;
    });
  }

  function evaluatePrediction(prediction,rows){
    if(prediction.evaluated)return prediction;

    const originIndex=findOriginIndex(rows,prediction);
    if(originIndex<0)return prediction;

    const targetIndex=originIndex+prediction.horizon;
    if(targetIndex>=rows.length)return prediction;

    const actualRow=rows[targetIndex];
    const actualNav=actualRow.nav;
    const actualDirection=Math.sign(actualNav-prediction.originNav);
    const predictedDirection=Math.sign(
      prediction.integratedPrediction-prediction.originNav
    );

    const modelResults=prediction.modelPredictions.map(model=>{
      const errorPct=Math.abs(model.predicted-actualNav)/actualNav*100;
      const signedErrorPct=(model.predicted-actualNav)/actualNav*100;
      const directionCorrect=
        Math.sign(model.predicted-prediction.originNav)===actualDirection;
      const intervalHit=
        actualNav>=model.p05&&actualNav<=model.p95;

      return {
        ...model,
        errorPct,
        signedErrorPct,
        directionCorrect,
        intervalHit
      };
    });

    return {
      ...prediction,
      evaluated:true,
      actualNav,
      actualDate:actualRow.dateText,
      targetDate:actualRow.dateText,
      integratedErrorPct:
        Math.abs(prediction.integratedPrediction-actualNav)/actualNav*100,
      integratedSignedErrorPct:
        (prediction.integratedPrediction-actualNav)/actualNav*100,
      directionCorrect:predictedDirection===actualDirection,
      intervalHit:
        actualNav>=prediction.integratedLow&&
        actualNav<=prediction.integratedHigh,
      modelResults
    };
  }

  function aggregateModelStats(predictions){
    const evaluated=predictions.filter(item=>item.evaluated);
    const grouped={};

    for(const prediction of evaluated){
      for(const model of prediction.modelResults||[]){
        if(!grouped[model.id]){
          grouped[model.id]={
            id:model.id,
            label:model.label,
            count:0,
            errors:[],
            signedErrors:[],
            directionHits:0,
            intervalHits:0
          };
        }

        const group=grouped[model.id];
        group.count+=1;
        group.errors.push(model.errorPct);
        group.signedErrors.push(model.signedErrorPct);
        if(model.directionCorrect)group.directionHits+=1;
        if(model.intervalHit)group.intervalHits+=1;
      }
    }

    const stats=Object.values(grouped).map(group=>{
      const mape=mean(group.errors);
      const bias=mean(group.signedErrors);
      const directionHit=group.count
        ?group.directionHits/group.count*100
        :0;
      const intervalCoverage=group.count
        ?group.intervalHits/group.count*100
        :0;

      const score=clamp(
        (100-mape*5)*.50+
        directionHit*.30+
        (100-Math.abs(bias)*6)*.10+
        intervalCoverage*.10,
        0,
        100
      );

      return {
        id:group.id,
        label:group.label,
        count:group.count,
        mape,
        bias,
        directionHit,
        intervalCoverage,
        score
      };
    });

    const rawWeights=stats.map(stat=>
      1/Math.max(stat.mape,.5)**2
    );
    const total=rawWeights.reduce((sum,value)=>sum+value,0)||1;

    return stats
      .map((stat,index)=>({
        ...stat,
        weight:rawWeights[index]/total
      }))
      .sort((left,right)=>right.score-left.score);
  }

  function evaluateAll(rows){
    const state=loadState();
    const predictions=state.predictions.map(item=>
      evaluatePrediction(item,rows)
    );
    const modelStats=aggregateModelStats(predictions);

    const next={
      ...state,
      predictions,
      modelStats:Object.fromEntries(
        modelStats.map(stat=>[stat.id,stat])
      )
    };

    saveState(next);
    return next;
  }

  function addPrediction(prediction){
    const state=loadState();
    state.predictions.unshift(prediction);
    state.predictions=state.predictions.slice(0,MAX_PREDICTIONS);
    saveState(state);
    return state;
  }

  function getModelWeights(){
    const state=loadState();
    const stats=Object.values(state.modelStats||{});
    if(!stats.length)return null;

    const total=stats.reduce((sum,stat)=>sum+(stat.weight||0),0)||1;
    return Object.fromEntries(
      stats.map(stat=>[stat.id,(stat.weight||0)/total])
    );
  }

  function summary(state){
    const evaluated=state.predictions.filter(item=>item.evaluated);
    const pending=state.predictions.filter(item=>!item.evaluated);
    const integratedMape=evaluated.length
      ?mean(evaluated.map(item=>item.integratedErrorPct))
      :0;
    const directionHit=evaluated.length
      ?evaluated.filter(item=>item.directionCorrect).length/
        evaluated.length*100
      :0;
    const intervalCoverage=evaluated.length
      ?evaluated.filter(item=>item.intervalHit).length/
        evaluated.length*100
      :0;

    return {
      total:state.predictions.length,
      evaluated:evaluated.length,
      pending:pending.length,
      integratedMape,
      directionHit,
      intervalCoverage,
      modelStats:Object.values(state.modelStats||{})
        .sort((a,b)=>b.score-a.score)
    };
  }

  return Object.freeze({
    loadState,
    saveState,
    clear,
    createPrediction,
    addPrediction,
    evaluateAll,
    getModelWeights,
    summary
  });
})();

function saveCurrentPrediction(){
  const status=$("learningStatus");

  try{
    if(!last.advisor){
      throw new Error("先に「総合判断」を実行してください。");
    }

    const prediction=LearningSystem.createPrediction(
      last.advisor,
      last.d
    );

    const state=LearningSystem.addPrediction(prediction);
    renderLearningSystem(state);

    status.className="status ok";
    status.textContent="現在の予測を保存しました。CSV更新後に実績照合できます。";
  }catch(error){
    status.className="status bad";
    status.textContent=`保存エラー：${error.message}`;
  }
}

function evaluateSavedPredictions(){
  const status=$("learningStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  try{
    const before=LearningSystem.summary(
      LearningSystem.loadState()
    );
    const state=LearningSystem.evaluateAll(last.d);
    const after=LearningSystem.summary(state);
    const newlyEvaluated=after.evaluated-before.evaluated;

    renderLearningSystem(state);

    status.className="status ok";
    status.textContent=newlyEvaluated>0
      ?`${newlyEvaluated}件の予測を新しく実績照合しました。`
      :"照合可能な新しい予測はありませんでした。";
  }catch(error){
    console.error(error);
    status.className="status bad";
    status.textContent=`実績照合エラー：${error.message}`;
  }
}

function clearLearningData(){
  if(!confirm("予測履歴と学習データをすべて消去しますか？")){
    return;
  }

  LearningSystem.clear();
  renderLearningSystem(LearningSystem.loadState());

  $("learningStatus").className="status";
  $("learningStatus").textContent="学習データを消去しました。";
}

function learningClass(score){
  if(score>=75)return "learning-good";
  if(score>=55)return "learning-mid";
  return "learning-bad";
}

function renderLearningSystem(state=null){
  const currentState=state||LearningSystem.loadState();
  const summary=LearningSystem.summary(currentState);
  const best=summary.modelStats[0];

  $("learningCards").innerHTML=`
    <div class="card">
      <div class="card-title">保存予測</div>
      <div class="card-value">${summary.total}</div>
    </div>
    <div class="card">
      <div class="card-title">実績照合済み</div>
      <div class="card-value">${summary.evaluated}</div>
    </div>
    <div class="card">
      <div class="card-title">未到来</div>
      <div class="card-value">${summary.pending}</div>
    </div>
    <div class="card">
      <div class="card-title">統合予測MAPE</div>
      <div class="card-value">${summary.evaluated?summary.integratedMape.toFixed(2):"—"}${summary.evaluated?"%":""}</div>
    </div>`;

  $("learningComment").textContent=summary.evaluated
    ?`学習結果

統合予測の方向的中率：
${summary.directionHit.toFixed(1)}%

予測区間カバー率：
${summary.intervalCoverage.toFixed(1)}%

現在の最優秀モデル：
${best?.label||"判定不能"}
信頼度 ${best?.score.toFixed(0)||"0"}点

照合件数が少ない間は、学習済み重みを強く信頼しすぎないでください。`
    :"まだ実績照合済みの予測がありません。総合判断を保存し、予測期間が経過した後にCSVを更新して実績照合してください。";

  $("learningTable").innerHTML=summary.modelStats.length
    ?`<div class="tablewrap">
      <table>
        <thead>
          <tr>
            <th>モデル</th>
            <th>件数</th>
            <th>信頼度</th>
            <th>MAPE</th>
            <th>方向的中</th>
            <th>区間カバー</th>
            <th>偏り</th>
          </tr>
        </thead>
        <tbody>
          ${summary.modelStats.map(stat=>`
            <tr>
              <td>${stat.label}</td>
              <td>${stat.count}</td>
              <td class="${learningClass(stat.score)}">${stat.score.toFixed(0)}点</td>
              <td>${stat.mape.toFixed(2)}%</td>
              <td>${stat.directionHit.toFixed(1)}%</td>
              <td>${stat.intervalCoverage.toFixed(1)}%</td>
              <td>${stat.bias>=0?"+":""}${stat.bias.toFixed(2)}%</td>
            </tr>`).join("")}
        </tbody>
      </table>
    </div>`
    :'<div class="small">モデル成績はまだありません。</div>';

  $("learningWeights").innerHTML=summary.modelStats.map(stat=>`
    <div class="weight-row">
      <span>${stat.label}</span>
      <div class="weight-bar">
        <span style="width:${(stat.weight||0)*100}%"></span>
      </div>
      <strong>${((stat.weight||0)*100).toFixed(1)}%</strong>
    </div>`).join("");

  $("predictionHistory").innerHTML=currentState.predictions.length
    ?currentState.predictions.map(item=>`
      <div class="prediction-item">
        <div class="prediction-head">
          <span>${item.originDate} → ${item.horizon}営業日後</span>
          <span>${item.evaluated?"照合済み":"未到来"}</span>
        </div>
        <div class="prediction-meta">
          総合予測：${Math.round(item.integratedPrediction).toLocaleString()}円<br>
          判断：${item.advisorAction}・スコア ${item.advisorScore.toFixed(0)}点<br>
          ${item.evaluated
            ?`実績：${Math.round(item.actualNav).toLocaleString()}円（${item.actualDate}）<br>
              誤差：${item.integratedErrorPct.toFixed(2)}%・方向 ${item.directionCorrect?"的中":"不的中"}`
            :"予測期間の実績データがCSVへ追加されると照合できます。"}
        </div>
      </div>`).join("")
    :'<div class="small">保存済み予測はありません。</div>';

  let report;

  if(!summary.evaluated){
    report="まだ学習結果はありません。予測を保存し、期間経過後にCSVを更新して実績照合を行ってください。";
  }else{
    const worst=summary.modelStats.at(-1);
    report=`AI学習レポート

最も成績が良いモデル：
${best.label}
MAPE ${best.mape.toFixed(2)}%
方向的中率 ${best.directionHit.toFixed(1)}%

最も成績が低いモデル：
${worst.label}
MAPE ${worst.mape.toFixed(2)}%

統合予測：
MAPE ${summary.integratedMape.toFixed(2)}%
方向的中率 ${summary.directionHit.toFixed(1)}%

今後は、成績の良いモデルへ大きな重みを付ける参考データとして使用します。相場局面が変わると過去の優秀モデルが機能しなくなる場合があります。`;
  }

  $("learningReport").textContent=report;
}


const AccuracyMeasurementEngine=(()=>{
  const models=[
    {id:"historical",label:"過去平均"},
    {id:"ewma",label:"EWMA"},
    {id:"momentum",label:"モメンタム"},
    {id:"mean-reversion",label:"平均回帰"},
    {id:"equal-ensemble",label:"均等アンサンブル"}
  ];

  function grade(score){
    if(score>=85)return {grade:"S",label:"非常に高い"};
    if(score>=75)return {grade:"A",label:"高い"};
    if(score>=65)return {grade:"B",label:"比較的良好"};
    if(score>=55)return {grade:"C",label:"標準"};
    if(score>=40)return {grade:"D",label:"低め"};
    return {grade:"E",label:"不十分"};
  }

  function calcMetrics(records,targetCoverage){
    if(!records.length)return {count:0,mape:0,rmsePct:0,biasPct:0,directionHit:0,coverage:0,score:0};
    const errors=records.map(r=>Math.abs(r.predicted-r.actual)/r.actual*100);
    const signed=records.map(r=>(r.predicted-r.actual)/r.actual*100);
    const directionHit=records.filter(r=>Math.sign(r.predicted-r.origin)===Math.sign(r.actual-r.origin)).length/records.length*100;
    const coverage=records.filter(r=>r.actual>=r.low&&r.actual<=r.high).length/records.length*100;
    const mape=mean(errors);
    const rmsePct=Math.sqrt(mean(signed.map(v=>v*v)));
    const biasPct=mean(signed);
    const score=clamp(
      clamp(100-mape*7,0,100)*.35+
      clamp(100-rmsePct*5,0,100)*.20+
      clamp((directionHit-45)*2.2,0,100)*.25+
      clamp(100-Math.abs(coverage-targetCoverage)*3,0,100)*.12+
      clamp(100-Math.abs(biasPct)*8,0,100)*.08,
      0,100
    );
    return {count:records.length,mape,rmsePct,biasPct,directionHit,coverage,score};
  }

  function classify(trainingRows){
    try{
      const features=MarketRegimeEngine.featureVector(trainingRows.slice(-Math.min(63,trainingRows.length)));
      return MarketRegimeEngine.classify(features).regime;
    }catch{return "unknown"}
  }

  function run(rows,options={}){
    const horizon=Math.max(1,+options.horizon||21);
    const lookback=Math.max(60,+options.lookback||120);
    const step=Math.max(1,+options.step||5);
    const interval=clamp(+options.interval||.90,.5,.99);
    const minimum=Math.max(lookback,Math.min(63,lookback));
    if(rows.length<minimum+horizon){
      throw new Error(`現在の設定には${minimum+horizon}営業日必要です。自動モードで設定を調整してください。`);
    }

    const byModel=Object.fromEntries(models.map(m=>[m.id,[]]));
    const integrated=[];
    const byRegime={};
    const byYear={};

    for(let originIndex=minimum-1;originIndex+horizon<rows.length;originIndex+=step){
      const training=rows.slice(Math.max(0,originIndex-lookback+1),originIndex+1);
      const origin=rows[originIndex];
      const actual=rows[originIndex+horizon];
      const predictions=ForecastValidationEngine.predictAll(training,horizon,interval);
      const regime=classify(training);
      const records=[];

      for(const model of models){
        const p=predictions[model.id];
        const record={modelId:model.id,modelLabel:model.label,date:origin.date,dateText:origin.dateText,origin:origin.nav,actual:actual.nav,actualDate:actual.dateText,predicted:p.center,low:p.low,high:p.high,regime};
        byModel[model.id].push(record);
        records.push(record);
      }

      const weights=LearningSystem.getModelWeights();
      let center=0,low=0,high=0,total=0;
      for(const r of records){
        const w=weights?.[r.modelId]||1;
        center+=r.predicted*w; low+=r.low*w; high+=r.high*w; total+=w;
      }
      const item={date:origin.date,dateText:origin.dateText,origin:origin.nav,actual:actual.nav,actualDate:actual.dateText,predicted:center/(total||1),low:low/(total||1),high:high/(total||1),regime};
      integrated.push(item);
      (byRegime[regime]??=[]).push(item);
      const year=origin.date instanceof Date?origin.date.getFullYear():String(origin.dateText).slice(0,4);
      (byYear[year]??=[]).push(item);
    }

    const modelResults=models.map(m=>({...m,metrics:calcMetrics(byModel[m.id],interval*100),records:byModel[m.id]})).sort((a,b)=>b.metrics.score-a.metrics.score);
    const integratedMetrics=calcMetrics(integrated,interval*100);
    const regimeResults=Object.entries(byRegime).map(([regime,records])=>({regime,metrics:calcMetrics(records,interval*100)})).sort((a,b)=>b.metrics.score-a.metrics.score);
    const periodResults=Object.entries(byYear).map(([year,records])=>({year,metrics:calcMetrics(records,interval*100)})).sort((a,b)=>String(a.year).localeCompare(String(b.year)));
    return {
      horizon,lookback,step,interval,
      integratedMetrics,integratedRecords:integrated,
      modelResults,regimeResults,periodResults,
      grade:grade(integratedMetrics.score),
      bestModel:modelResults[0],weakestModel:modelResults.at(-1),
      bestRegime:regimeResults[0],weakestRegime:regimeResults.at(-1),
      sampleCount:integrated.length
    };
  }
  return Object.freeze({run});
})();

function measurementClass(score){
  if(score>=85)return "measurement-excellent";
  if(score>=75)return "measurement-good";
  if(score>=60)return "measurement-fair";
  if(score>=45)return "measurement-weak";
  return "measurement-poor";
}

function runAccuracyMeasurement(){
  const status=$("measurementStatus");
  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }
  status.className="status";
  status.textContent="過去データで予測を繰り返し、精度を測定しています…";
  setTimeout(()=>{
    try{
      const autoSettings=DataAdaptiveMode.bestValidationSettings(
        last.d.length,
        {
          horizon:+$("measureHorizon").value,
          lookback:+$("measureLookback").value,
          step:+$("measureStep").value
        }
      );

      const result=AccuracyMeasurementEngine.run(last.d,{
        horizon:autoSettings.horizon,
        lookback:autoSettings.lookback,
        step:autoSettings.step,
        interval:+$("measureInterval").value
      });

      result.autoSettings=autoSettings;
      last.measurement=result;
      renderAccuracyMeasurement(result);
      status.className="status ok";
      status.textContent=`精度測定が完了しました。測定回数：${result.sampleCount}回`;
    }catch(error){
      console.error(error);
      status.className="status bad";
      status.textContent=`精度測定エラー：${error.message}`;
    }
  },50);
}

function renderAccuracyMeasurement(result){
  const m=result.integratedMetrics;
  $("measurementHero").innerHTML=`<div class="measurement-score ${measurementClass(m.score)}">${m.score.toFixed(0)}点</div><div class="measurement-grade">精度ランク ${result.grade.grade}</div><div class="small" style="margin-top:8px">${result.grade.label}・測定回数 ${result.sampleCount}回</div>`;
  $("measurementScoreBar").innerHTML=`<div class="scorebar"><span style="width:${m.score}%"></span></div>`;
  $("measurementCards").innerHTML=`
    <div class="card"><div class="card-title">方向的中率</div><div class="card-value">${m.directionHit.toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">MAPE</div><div class="card-value">${m.mape.toFixed(2)}%</div></div>
    <div class="card"><div class="card-title">RMSE</div><div class="card-value">${m.rmsePct.toFixed(2)}%</div></div>
    <div class="card"><div class="card-title">区間カバー率</div><div class="card-value">${m.coverage.toFixed(1)}%</div></div>
    <div class="card"><div class="card-title">予測バイアス</div><div class="card-value">${m.biasPct>=0?"+":""}${m.biasPct.toFixed(2)}%</div></div>
    <div class="card"><div class="card-title">測定回数</div><div class="card-value">${result.sampleCount}</div></div>`;

  $("measurementModelTable").innerHTML=`<div class="tablewrap"><table><thead><tr><th>モデル</th><th>精度点</th><th>MAPE</th><th>RMSE</th><th>方向的中</th><th>区間カバー</th><th>偏り</th></tr></thead><tbody>${result.modelResults.map(x=>`<tr><td>${x.label}</td><td class="${measurementClass(x.metrics.score)}">${x.metrics.score.toFixed(0)}点</td><td>${x.metrics.mape.toFixed(2)}%</td><td>${x.metrics.rmsePct.toFixed(2)}%</td><td>${x.metrics.directionHit.toFixed(1)}%</td><td>${x.metrics.coverage.toFixed(1)}%</td><td>${x.metrics.biasPct>=0?"+":""}${x.metrics.biasPct.toFixed(2)}%</td></tr>`).join("")}</tbody></table></div>`;

  $("measurementRegimeTable").innerHTML=`<div class="tablewrap"><table><thead><tr><th>相場局面</th><th>件数</th><th>精度点</th><th>MAPE</th><th>方向的中</th><th>区間カバー</th></tr></thead><tbody>${result.regimeResults.map(x=>`<tr><td>${regimeLabel(x.regime)}</td><td>${x.metrics.count}</td><td class="${measurementClass(x.metrics.score)}">${x.metrics.score.toFixed(0)}点</td><td>${x.metrics.mape.toFixed(2)}%</td><td>${x.metrics.directionHit.toFixed(1)}%</td><td>${x.metrics.coverage.toFixed(1)}%</td></tr>`).join("")}</tbody></table></div>`;

  $("measurementRegimeComment").textContent=`最も得意な局面：${regimeLabel(result.bestRegime?.regime||"unknown")}（${result.bestRegime?.metrics.score.toFixed(0)||0}点）
最も苦手な局面：${regimeLabel(result.weakestRegime?.regime||"unknown")}（${result.weakestRegime?.metrics.score.toFixed(0)||0}点）`;

  $("measurementPeriodTable").innerHTML=`<div class="tablewrap"><table><thead><tr><th>年</th><th>件数</th><th>精度点</th><th>MAPE</th><th>方向的中</th><th>区間カバー</th></tr></thead><tbody>${result.periodResults.map(x=>`<tr><td>${x.year}</td><td>${x.metrics.count}</td><td class="${measurementClass(x.metrics.score)}">${x.metrics.score.toFixed(0)}点</td><td>${x.metrics.mape.toFixed(2)}%</td><td>${x.metrics.directionHit.toFixed(1)}%</td><td>${x.metrics.coverage.toFixed(1)}%</td></tr>`).join("")}</tbody></table></div>`;

  const recent=result.integratedRecords.slice(-Math.min(80,result.integratedRecords.length));
  lineChart($("measurementChart"),[
    {name:"実績",color:"#22c55e",values:recent.map(r=>r.actual)},
    {name:"予測",color:"#3b82f6",values:recent.map(r=>r.predicted)}
  ]);

  let reliability=m.directionHit>=65&&m.mape<=5
    ?"方向性と価格誤差の両方が良好で、比較的信頼できる水準です。"
    :m.directionHit>=55&&m.mape<=10
      ?"参考に使える水準ですが、単一の予測値へ依存しない方が安全です。"
      :"予測の不確実性が高いため、予測値よりリスク範囲を重視してください。";

  $("measurementSummary").textContent=`方向的中率 ${m.directionHit.toFixed(1)}%
平均価格誤差 ${m.mape.toFixed(2)}%
RMSE ${m.rmsePct.toFixed(2)}%
${Math.round(result.interval*100)}%区間カバー率 ${m.coverage.toFixed(1)}%

${reliability}`;

  $("measurementReport").textContent=`予測精度評価レポート

予測期間 ${result.horizon}営業日
学習期間 ${result.lookback}営業日
測定間隔 ${result.step}営業日
測定回数 ${result.sampleCount}回

総合精度 ${m.score.toFixed(0)}点・ランク${result.grade.grade}

最優秀モデル：${result.bestModel.label}
精度 ${result.bestModel.metrics.score.toFixed(0)}点
MAPE ${result.bestModel.metrics.mape.toFixed(2)}%

最も精度が低いモデル：${result.weakestModel.label}
精度 ${result.weakestModel.metrics.score.toFixed(0)}点

過去データでの精度であり、将来の精度を保証するものではありません。`;
}


/* =========================================================
   Ver.18 Statistical Forecast Engine
   ========================================================= */

const StatisticalForecastEngine=(()=>{
  function logReturns(rows){
    const values=[];
    for(let index=1;index<rows.length;index++){
      const previous=rows[index-1].nav;
      const current=rows[index].nav;
      if(previous>0&&current>0){
        values.push(Math.log(current/previous));
      }
    }
    return values;
  }

  function ewmaVariance(values,lambda=.94){
    if(!values.length)return 0;
    let varianceValue=values[0]*values[0];
    for(let index=1;index<values.length;index++){
      varianceValue=lambda*varianceValue+
        (1-lambda)*values[index-1]*values[index-1];
    }
    return Math.max(varianceValue,0);
  }

  function garchVarianceForecast(values,horizon){
    if(values.length<10)return sd(values)**2;

    const longVariance=variance(values,false);
    let conditional=ewmaVariance(values,.94);
    const alpha=.09;
    const beta=.88;
    const omega=Math.max(longVariance*(1-alpha-beta),1e-10);

    let sum=0;
    let lastShock=values.at(-1)**2;

    for(let step=0;step<horizon;step++){
      conditional=omega+alpha*lastShock+beta*conditional;
      sum+=conditional;
      lastShock=conditional;
    }

    return sum/Math.max(horizon,1);
  }

  function estimateStudentDf(values){
    const kurt=excessKurtosis(values);
    if(kurt<=0)return 30;
    return clamp(6/kurt+4,4.1,30);
  }

  function zValue(interval){
    if(interval>=.949)return 1.96;
    if(interval>=.899)return 1.645;
    return 1.282;
  }

  function tMultiplier(df,interval){
    const z=zValue(interval);
    const correction=1+(z*z+1)/(4*df);
    return z*correction;
  }

  function driftEstimate(values,mode){
    const historical=mean(values);
    const recent=mean(values.slice(-Math.min(21,values.length)));

    if(mode==="garch")return historical*.45+recent*.25;
    if(mode==="student-t")return historical*.40+recent*.30;
    if(mode==="regime")return historical*.30+recent*.55;
    return historical*.40+recent*.35;
  }

  function regimeAdjustment(regime){
    return {
      bull:.00035,
      neutral:0,
      bear:-.00035,
      volatile:-.00010
    }[regime]||0;
  }

  function forecastModel(rows,horizon,interval,modelId,regime){
    const returnsValue=logReturns(rows);
    if(returnsValue.length<20){
      throw new Error("統計予測には20営業日以上のデータが必要です。");
    }

    const latest=rows.at(-1).nav;
    let dailyDrift=driftEstimate(returnsValue,modelId);
    let dailyVariance=variance(returnsValue,false);
    let multiplier=zValue(interval);
    let df=null;

    if(modelId==="garch"){
      dailyVariance=garchVarianceForecast(returnsValue,horizon);
    }

    if(modelId==="student-t"){
      df=estimateStudentDf(returnsValue);
      multiplier=tMultiplier(df,interval);
      dailyVariance=variance(returnsValue,false);
    }

    if(modelId==="regime"){
      dailyDrift+=regimeAdjustment(regime);
      const regimeScale={
        bull:.90,
        neutral:1,
        bear:1.15,
        volatile:1.45
      }[regime]||1;
      dailyVariance=ewmaVariance(returnsValue,.92)*regimeScale;
    }

    const center=latest*Math.exp(dailyDrift*horizon);
    const spread=multiplier*Math.sqrt(
      Math.max(dailyVariance,0)*horizon
    );

    return {
      id:modelId,
      center,
      low:latest*Math.exp(dailyDrift*horizon-spread),
      high:latest*Math.exp(dailyDrift*horizon+spread),
      dailyDrift,
      annualizedVol:Math.sqrt(Math.max(dailyVariance,0))*Math.sqrt(252)*100,
      df
    };
  }

  function measurementWeights(){
    const measurement=last.measurement;
    if(!measurement?.modelResults?.length)return null;

    const raw={};
    for(const model of measurement.modelResults){
      raw[model.id]=Math.max(model.metrics.score,5);
    }

    const total=Object.values(raw).reduce((sum,value)=>sum+value,0)||1;
    return Object.fromEntries(
      Object.entries(raw).map(([key,value])=>[key,value/total])
    );
  }

  function ensemble(models,regime){
    const learning=LearningSystem.getModelWeights();
    const measurement=measurementWeights();
    const selfLearningWeights=SelfLearningAI.effectiveWeights(
      regime,
      +$("futureChartHorizon")?.value||21
    );

    const modelWeightMap={
      garch:.28,
      "student-t":.25,
      regime:.27,
      baseline:.20
    };

    if(regime==="volatile"){
      modelWeightMap["student-t"]+=.10;
      modelWeightMap.garch+=.05;
      modelWeightMap.baseline-=.10;
      modelWeightMap.regime-=.05;
    }else if(regime==="bull"||regime==="bear"){
      modelWeightMap.regime+=.10;
      modelWeightMap.baseline-=.05;
      modelWeightMap.garch-=.05;
    }

    if(learning){
      const qualityBoost=Math.min(
        Object.values(learning).reduce((sum,value)=>sum+value,0),
        1
      );
      modelWeightMap.baseline+=qualityBoost*.05;
    }

    if(measurement){
      const averageScore=mean(
        last.measurement.modelResults.map(item=>item.metrics.score)
      );
      if(averageScore<55){
        modelWeightMap["student-t"]+=.05;
        modelWeightMap.garch+=.05;
        modelWeightMap.baseline-=.10;
      }
    }

    if(selfLearningWeights){
      modelWeightMap.garch=
        modelWeightMap.garch*.55+
        (selfLearningWeights.garch||0)*.45;
      modelWeightMap["student-t"]=
        modelWeightMap["student-t"]*.55+
        (selfLearningWeights["student-t"]||0)*.45;
      modelWeightMap.regime=
        modelWeightMap.regime*.55+
        (selfLearningWeights.regime||0)*.45;
      modelWeightMap.baseline=
        modelWeightMap.baseline*.55+
        (selfLearningWeights.baseline||0)*.45;
    }

    const total=Object.values(modelWeightMap)
      .reduce((sum,value)=>sum+Math.max(value,0),0)||1;

    const normalized=Object.fromEntries(
      Object.entries(modelWeightMap).map(
        ([key,value])=>[key,Math.max(value,0)/total]
      )
    );

    const lookup=Object.fromEntries(models.map(model=>[model.id,model]));
    const baseline=lookup.baseline;

    const center=
      lookup.garch.center*normalized.garch+
      lookup["student-t"].center*normalized["student-t"]+
      lookup.regime.center*normalized.regime+
      baseline.center*normalized.baseline;

    const low=
      lookup.garch.low*normalized.garch+
      lookup["student-t"].low*normalized["student-t"]+
      lookup.regime.low*normalized.regime+
      baseline.low*normalized.baseline;

    const high=
      lookup.garch.high*normalized.garch+
      lookup["student-t"].high*normalized["student-t"]+
      lookup.regime.high*normalized.regime+
      baseline.high*normalized.baseline;

    return {
      id:"ensemble",
      center,
      low,
      high,
      annualizedVol:mean(models.map(model=>model.annualizedVol)),
      weights:normalized
    };
  }

  function selectModel(models,regime,diagnostics){
    const byId=Object.fromEntries(models.map(model=>[model.id,model]));

    if(diagnostics.excessKurtosis>3||regime==="volatile"){
      return {
        id:"student-t",
        reason:"裾の厚さまたは高ボラ局面が強いため、t分布を優先しました。"
      };
    }

    if(Math.abs(diagnostics.lag1Autocorrelation)>.12){
      return {
        id:"regime",
        reason:"短期の連続性が比較的強いため、レジーム切替モデルを優先しました。"
      };
    }

    if(diagnostics.volatilityRatio>1.25){
      return {
        id:"garch",
        reason:"直近ボラティリティが長期平均を上回るため、GARCH風モデルを優先しました。"
      };
    }

    return {
      id:"ensemble",
      reason:"単一の特徴が支配的でないため、精度加重アンサンブルを選択しました。"
    };
  }

  function diagnose(rows){
    const values=logReturns(rows);
    const recent=values.slice(-Math.min(21,values.length));
    const long=values.slice(-Math.min(252,values.length));
    const recentVol=sd(recent);
    const longVol=sd(long);

    return {
      annualizedVol:sd(values)*Math.sqrt(252)*100,
      recentAnnualizedVol:recentVol*Math.sqrt(252)*100,
      volatilityRatio:longVol?recentVol/longVol:1,
      skewness:skewness(values),
      excessKurtosis:excessKurtosis(values),
      lag1Autocorrelation:autocorrelation(values,1),
      estimatedDf:estimateStudentDf(values)
    };
  }

  function run(rows,options={}){
    const horizon=Math.max(1,+options.horizon||21);
    const lookback=Math.max(60,+options.lookback||252);
    const interval=clamp(+options.interval||.90,.5,.99);
    const requested=options.model||"auto";
    const training=rows.slice(-Math.min(lookback,rows.length));

    const regimeResult=MarketRegimeEngine.analyze(rows,{
      window:Math.min(63,lookback),
      horizon:Math.min(horizon,63),
      count:5
    });

    const regime=regimeResult.classification.regime;
    const diagnostics=diagnose(training);

    const baselinePrediction=ForecastValidationEngine.predictAll(
      training,
      horizon,
      interval
    )["equal-ensemble"];

    const models=[
      forecastModel(training,horizon,interval,"garch",regime),
      forecastModel(training,horizon,interval,"student-t",regime),
      forecastModel(training,horizon,interval,"regime",regime),
      {
        id:"baseline",
        center:baselinePrediction.center,
        low:baselinePrediction.low,
        high:baselinePrediction.high,
        annualizedVol:diagnostics.annualizedVol
      }
    ];

    const ensembleResult=ensemble(models,regime);
    const allModels=[...models,ensembleResult];

    const automatic=selectModel(allModels,regime,diagnostics);
    const selectedId=requested==="auto"?automatic.id:requested;
    const selected=allModels.find(model=>model.id===selectedId)
      ||ensembleResult;

    return {
      horizon,
      lookback,
      interval,
      requested,
      selected,
      selectedId,
      automatic,
      regime,
      regimeResult,
      diagnostics,
      models:allModels
    };
  }

  return Object.freeze({
    run,
    diagnose,
    forecastModel
  });
})();

function statModelLabel(id){
  return {
    garch:"GARCH風",
    "student-t":"t分布",
    regime:"レジーム切替",
    baseline:"従来アンサンブル",
    ensemble:"精度加重アンサンブル"
  }[id]||id;
}

function runStatisticalForecast(){
  const status=$("statStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  status.className="status";
  status.textContent="統計モデルを診断し、予測を作成しています…";

  setTimeout(()=>{
    try{
      const autoSettings=DataAdaptiveMode.bestStatSettings(
        last.d.length,
        {
          horizon:+$("statHorizon").value,
          model:$("statModel").value
        }
      );

      const result=StatisticalForecastEngine.run(last.d,{
        horizon:autoSettings.horizon,
        lookback:autoSettings.lookback,
        model:autoSettings.model,
        interval:+$("statInterval").value
      });

      result.autoSettings=autoSettings;

      last.statistics=result;
      renderStatisticalForecast(result);

      status.className="status ok";
      status.textContent="統計予測が完了しました。";
    }catch(error){
      console.error(error);
      status.className="status bad";
      status.textContent=`統計予測エラー：${error.message}`;
    }
  },50);
}

function renderStatisticalForecast(result){
  const selected=result.selected;
  const latest=last.d.at(-1).nav;
  const forecastReturn=(selected.center/latest-1)*100;

  $("statChoiceCards").innerHTML=`
    <div class="card">
      <div class="card-title">選択モデル</div>
      <div class="card-value stat-auto">${statModelLabel(result.selectedId)}</div>
    </div>
    <div class="card">
      <div class="card-title">現在局面</div>
      <div class="card-value">${regimeLabel(result.regime)}</div>
    </div>
    <div class="card">
      <div class="card-title">推定自由度</div>
      <div class="card-value">${result.diagnostics.estimatedDf.toFixed(1)}</div>
    </div>
    <div class="card">
      <div class="card-title">直近/長期ボラ比</div>
      <div class="card-value">${result.diagnostics.volatilityRatio.toFixed(2)}</div>
    </div>`;

  $("statChoiceComment").textContent=result.requested==="auto"
    ?`自動選択理由

${result.automatic.reason}

現在の局面：
${regimeLabel(result.regime)}

超過尖度：
${result.diagnostics.excessKurtosis.toFixed(2)}

1日自己相関：
${result.diagnostics.lag1Autocorrelation.toFixed(3)}`
    :`手動で${statModelLabel(result.selectedId)}を選択しています。自動判定では${statModelLabel(result.automatic.id)}が推奨されています。

${result.automatic.reason}`;

  $("statForecastCards").innerHTML=`
    <div class="card">
      <div class="card-title">現在基準価額</div>
      <div class="card-value">${Math.round(latest).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">中心予測</div>
      <div class="card-value">${Math.round(selected.center).toLocaleString()}円</div>
      <div class="card-sub">${pct(forecastReturn)}</div>
    </div>
    <div class="card">
      <div class="card-title">予測下限</div>
      <div class="card-value">${Math.round(selected.low).toLocaleString()}円</div>
    </div>
    <div class="card">
      <div class="card-title">予測上限</div>
      <div class="card-value">${Math.round(selected.high).toLocaleString()}円</div>
    </div>`;

  lineChart(
    $("statChart"),
    [
      {
        name:"モデル中心値",
        color:"#3b82f6",
        values:result.models.map(model=>model.center)
      },
      {
        name:"モデル下限",
        color:"#f59e0b",
        values:result.models.map(model=>model.low)
      },
      {
        name:"モデル上限",
        color:"#22c55e",
        values:result.models.map(model=>model.high)
      }
    ]
  );

  $("statModelTable").innerHTML=`
    <div class="tablewrap">
      <table>
        <thead>
          <tr>
            <th>モデル</th>
            <th>中心予測</th>
            <th>下限</th>
            <th>上限</th>
            <th>年率ボラ</th>
          </tr>
        </thead>
        <tbody>
          ${result.models.map(model=>`
            <tr class="${model.id===result.selectedId?"stat-model-selected":""}">
              <td>${statModelLabel(model.id)}</td>
              <td>${Math.round(model.center).toLocaleString()}円</td>
              <td>${Math.round(model.low).toLocaleString()}円</td>
              <td>${Math.round(model.high).toLocaleString()}円</td>
              <td>${(model.annualizedVol||0).toFixed(1)}%</td>
            </tr>`).join("")}
        </tbody>
      </table>
    </div>`;

  const ensemble=result.models.find(model=>model.id==="ensemble");
  $("statModelComment").textContent=ensemble?.weights
    ?`精度加重アンサンブルの内部比率

GARCH風 ${(ensemble.weights.garch*100).toFixed(1)}%
t分布 ${(ensemble.weights["student-t"]*100).toFixed(1)}%
レジーム切替 ${(ensemble.weights.regime*100).toFixed(1)}%
従来モデル ${(ensemble.weights.baseline*100).toFixed(1)}%

相場局面とVer.17の精度測定結果に応じて重みを調整しています。`
    :"";

  $("statRiskCards").innerHTML=`
    <div class="card">
      <div class="card-title">長期年率ボラ</div>
      <div class="card-value">${result.diagnostics.annualizedVol.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">直近年率ボラ</div>
      <div class="card-value">${result.diagnostics.recentAnnualizedVol.toFixed(1)}%</div>
    </div>
    <div class="card">
      <div class="card-title">歪度</div>
      <div class="card-value">${result.diagnostics.skewness.toFixed(2)}</div>
    </div>
    <div class="card">
      <div class="card-title">超過尖度</div>
      <div class="card-value">${result.diagnostics.excessKurtosis.toFixed(2)}</div>
    </div>`;

  let riskText;
  if(result.diagnostics.volatilityRatio>1.3){
    riskText="直近の変動率が長期平均より高く、予測範囲を広めに見る必要があります。";
  }else if(result.diagnostics.excessKurtosis>3){
    riskText="急落・急騰が正規分布より多い傾向があるため、t分布の結果を重視してください。";
  }else{
    riskText="統計的な異常は比較的小さく、アンサンブル予測を中心に確認できます。";
  }

  $("statRiskComment").textContent=riskText;
}


/* =========================================================
   Ver.19 Adaptive AI
   ========================================================= */

const AdaptiveAIEngine=(()=>{
  const STORAGE_KEY="wcm19-adaptive-ai-v1";
  const MODEL_IDS=["iid","moving-block","stationary","random-block","hybrid"];
  const MODEL_LABELS={
    iid:"単日ブートストラップ",
    "moving-block":"移動ブロック法",
    stationary:"定常ブートストラップ",
    "random-block":"ランダム長ブロック",
    hybrid:"混合モデル"
  };

  function load(){
    try{
      const data=JSON.parse(localStorage.getItem(STORAGE_KEY)||"null");
      if(data&&data.version===1)return data;
    }catch(error){
      console.warn("Adaptive AI読込失敗",error);
    }
    return {
      version:1,
      weights:Object.fromEntries(MODEL_IDS.map(id=>[id,1/MODEL_IDS.length])),
      byRegime:{},
      byHorizon:{},
      history:[],
      confidence:0,
      sampleCount:0,
      updatedAt:null
    };
  }

  function save(state){
    localStorage.setItem(STORAGE_KEY,JSON.stringify(state));
  }

  function reset(){
    localStorage.removeItem(STORAGE_KEY);
  }

  function normalize(raw){
    const total=Object.values(raw).reduce((sum,value)=>sum+Math.max(value,0),0)||1;
    return Object.fromEntries(
      Object.entries(raw).map(([key,value])=>[
        key,
        Math.max(value,0)/total
      ])
    );
  }

  function recencyWeight(index,total,decay){
    const age=Math.max(total-index-1,0);
    return Math.pow(decay,age);
  }

  function scoreRecord(record){
    const errorScore=1/Math.max(record.errorPct||100,.5)**2;
    const directionBonus=record.directionCorrect?1.35:.70;
    const intervalBonus=record.intervalHit?1.10:.90;
    return errorScore*directionBonus*intervalBonus;
  }

  function collectLearningRecords(){
    const state=LearningSystem.loadState();
    const records=[];

    for(const prediction of state.predictions||[]){
      if(!prediction.evaluated)continue;
      for(const model of prediction.modelResults||[]){
        records.push({
          modelId:model.id,
          regime:prediction.regime||"unknown",
          horizon:prediction.horizon||21,
          errorPct:model.errorPct,
          directionCorrect:model.directionCorrect,
          intervalHit:model.intervalHit,
          actualDate:prediction.actualDate||prediction.targetDate||prediction.originDate
        });
      }
    }

    return records.sort((a,b)=>
      String(a.actualDate).localeCompare(String(b.actualDate))
    );
  }

  function buildWeights(records,decay,filterFn=()=>true){
    const filtered=records.filter(filterFn);
    const raw=Object.fromEntries(MODEL_IDS.map(id=>[id,.0001]));

    filtered.forEach((record,index)=>{
      if(!(record.modelId in raw))return;
      raw[record.modelId]+=
        scoreRecord(record)*
        recencyWeight(index,filtered.length,decay);
    });

    return {
      count:filtered.length,
      weights:normalize(raw)
    };
  }

  function measurementFallback(){
    const measurement=last.measurement;
    if(!measurement?.modelResults?.length)return null;

    const mapping={
      historical:"iid",
      ewma:"stationary",
      momentum:"moving-block",
      "mean-reversion":"random-block",
      "equal-ensemble":"hybrid"
    };

    const raw=Object.fromEntries(MODEL_IDS.map(id=>[id,.0001]));
    for(const item of measurement.modelResults){
      const id=mapping[item.id];
      if(id)raw[id]+=Math.max(item.metrics.score,1);
    }
    return normalize(raw);
  }

  function blendWeights(primary,fallback,primaryStrength){
    if(!fallback)return primary;
    const strength=clamp(primaryStrength,0,1);
    const raw={};
    for(const id of MODEL_IDS){
      raw[id]=(primary[id]||0)*strength+(fallback[id]||0)*(1-strength);
    }
    return normalize(raw);
  }

  function confidence(sampleCount,weights,minimum){
    const maxWeight=Math.max(...Object.values(weights));
    const concentration=clamp((maxWeight-.20)/.45,0,1);
    const sampleScore=clamp(sampleCount/Math.max(minimum*4,20),0,1);
    return clamp((sampleScore*.70+concentration*.30)*100,0,100);
  }

  function train({horizon=21,decay=.96,minimum=5}={}){
    const records=collectLearningRecords();
    const globalResult=buildWeights(records,decay);
    const fallback=measurementFallback();
    const strength=clamp(globalResult.count/Math.max(minimum*4,20),0,1);
    const weights=blendWeights(globalResult.weights,fallback,strength);

    const regimes=["bull","neutral","bear","volatile","unknown"];
    const byRegime={};
    for(const regime of regimes){
      const result=buildWeights(records,decay,r=>r.regime===regime);
      if(result.count){
        byRegime[regime]={
          count:result.count,
          weights:blendWeights(
            result.weights,
            weights,
            clamp(result.count/Math.max(minimum*2,10),0,1)
          )
        };
      }
    }

    const horizons=[5,21,63,126];
    const byHorizon={};
    for(const value of horizons){
      const result=buildWeights(records,decay,r=>Number(r.horizon)===value);
      if(result.count){
        byHorizon[value]={
          count:result.count,
          weights:blendWeights(
            result.weights,
            weights,
            clamp(result.count/Math.max(minimum*2,10),0,1)
          )
        };
      }
    }

    const aiConfidence=confidence(globalResult.count,weights,minimum);
    const previous=load();
    const snapshot={
      date:new Date().toISOString(),
      sampleCount:globalResult.count,
      confidence:aiConfidence,
      topModel:Object.entries(weights).sort((a,b)=>b[1]-a[1])[0][0],
      weights
    };

    const state={
      version:1,
      weights,
      byRegime,
      byHorizon,
      history:[snapshot,...(previous.history||[])].slice(0,30),
      confidence:aiConfidence,
      sampleCount:globalResult.count,
      updatedAt:snapshot.date,
      settings:{horizon,decay,minimum}
    };

    save(state);
    return state;
  }

  function effectiveWeights(regime,horizon){
    const state=load();
    let result={...state.weights};

    const regimeData=state.byRegime?.[regime];
    if(regimeData){
      result=blendWeights(
        regimeData.weights,
        result,
        clamp(regimeData.count/20,0,1)
      );
    }

    const horizonData=state.byHorizon?.[horizon];
    if(horizonData){
      result=blendWeights(
        horizonData.weights,
        result,
        clamp(horizonData.count/20,0,1)
      );
    }

    return normalize(result);
  }

  return Object.freeze({
    load,
    save,
    reset,
    train,
    effectiveWeights,
    labels:()=>({...MODEL_LABELS})
  });
})();

function runAdaptiveAI(){
  const status=$("adaptiveStatus");

  try{
    const state=AdaptiveAIEngine.train({
      horizon:+$("adaptiveHorizon").value||21,
      decay:+$("adaptiveDecay").value||.96,
      minimum:+$("adaptiveMinimum").value||5
    });

    renderAdaptiveAI(state);
    status.className="status ok";
    status.textContent=`Adaptive AIの学習が完了しました。学習件数：${state.sampleCount}件`;
  }catch(error){
    console.error(error);
    status.className="status bad";
    status.textContent=`Adaptive AI学習エラー：${error.message}`;
  }
}

function resetAdaptiveAI(){
  if(!confirm("Adaptive AIの重みと履歴を初期化しますか？"))return;
  AdaptiveAIEngine.reset();
  renderAdaptiveAI(AdaptiveAIEngine.load());
  $("adaptiveStatus").className="status";
  $("adaptiveStatus").textContent="Adaptive AIを初期化しました。";
}

function renderAdaptiveAI(state=null){
  const current=state||AdaptiveAIEngine.load();
  const labels=AdaptiveAIEngine.labels();
  const sorted=Object.entries(current.weights||{})
    .sort((a,b)=>b[1]-a[1]);
  const top=sorted[0]||["iid",.2];

  let stateLabel;
  if(current.confidence>=80)stateLabel="十分に学習";
  else if(current.confidence>=55)stateLabel="学習中";
  else if(current.confidence>0)stateLabel="初期学習";
  else stateLabel="未学習";

  $("adaptiveHero").innerHTML=`
    <div class="adaptive-score">${current.confidence.toFixed(0)}点</div>
    <div class="adaptive-state">AI信頼度・${stateLabel}</div>
    <div class="small" style="margin-top:8px">
      学習件数 ${current.sampleCount}件
    </div>`;

  $("adaptiveConfidenceBar").innerHTML=`
    <div class="scorebar">
      <span style="width:${current.confidence}%"></span>
    </div>`;

  $("adaptiveComment").textContent=current.sampleCount
    ?`現在最も重視しているモデル：
${labels[top[0]]}
重み ${(top[1]*100).toFixed(1)}%

最近の予測結果を強く反映し、相場局面と予測期間に応じて実効重みを変化させます。`
    :"実績照合済みの予測がまだありません。Ver.16のAI学習で予測を保存し、後日実績照合を行うと学習できます。";

  $("adaptiveWeights").innerHTML=sorted.map(([id,weight])=>`
    <div class="weight-row">
      <span>${labels[id]||id}</span>
      <div class="weight-bar"><span style="width:${weight*100}%"></span></div>
      <strong>${(weight*100).toFixed(1)}%</strong>
    </div>`).join("");

  $("adaptiveWeightComment").textContent=`Adaptive AIの重みは、平均誤差、方向的中、予測区間への収まり、最近の成績を組み合わせて計算します。

学習件数が少ない場合は、Ver.17の精度測定結果を補助的に使用します。`;

  const regimeNames={
    bull:"強気",
    neutral:"中立",
    bear:"弱気",
    volatile:"高ボラ",
    unknown:"不明"
  };

  const regimeRows=Object.entries(current.byRegime||{});
  $("adaptiveRegimeTable").innerHTML=regimeRows.length
    ?`<div class="tablewrap"><table>
      <thead><tr><th>局面</th><th>件数</th><th>最優秀モデル</th><th>重み</th></tr></thead>
      <tbody>${regimeRows.map(([regime,data])=>{
        const best=Object.entries(data.weights).sort((a,b)=>b[1]-a[1])[0];
        return `<tr>
          <td>${regimeNames[regime]||regime}</td>
          <td>${data.count}</td>
          <td>${labels[best[0]]||best[0]}</td>
          <td>${(best[1]*100).toFixed(1)}%</td>
        </tr>`;
      }).join("")}</tbody>
    </table></div>`
    :'<div class="small">局面別に分けるための学習データがまだありません。</div>';

  const horizonRows=Object.entries(current.byHorizon||{});
  $("adaptiveHorizonTable").innerHTML=horizonRows.length
    ?`<div class="tablewrap"><table>
      <thead><tr><th>期間</th><th>件数</th><th>最優秀モデル</th><th>重み</th></tr></thead>
      <tbody>${horizonRows.map(([horizon,data])=>{
        const best=Object.entries(data.weights).sort((a,b)=>b[1]-a[1])[0];
        return `<tr>
          <td>${horizon}営業日</td>
          <td>${data.count}</td>
          <td>${labels[best[0]]||best[0]}</td>
          <td>${(best[1]*100).toFixed(1)}%</td>
        </tr>`;
      }).join("")}</tbody>
    </table></div>`
    :'<div class="small">期間別に分けるための学習データがまだありません。</div>';

  $("adaptiveHistory").innerHTML=current.history?.length
    ?current.history.map(item=>`
      <div class="adaptive-history-item">
        <div class="adaptive-history-head">
          <span>${new Date(item.date).toLocaleString("ja-JP")}</span>
          <span>信頼度 ${item.confidence.toFixed(0)}点</span>
        </div>
        <div class="prediction-meta">
          学習件数：${item.sampleCount}件<br>
          最重要モデル：${labels[item.topModel]||item.topModel}
        </div>
      </div>`).join("")
    :'<div class="small">学習履歴はありません。</div>';
}


/* =========================================================
   Ver.20 Data-Adaptive Auto Mode
   ========================================================= */

const DataAdaptiveMode=(()=>{
  const MODES=[
    {
      id:"simple",
      label:"簡易AI",
      minDays:45,
      score:25,
      className:"mode-simple",
      description:"短期データだけで、方向性と変動率を簡易判定します。"
    },
    {
      id:"light",
      label:"軽量AI",
      minDays:70,
      score:45,
      className:"mode-light",
      description:"短期予測と簡易バックテストを利用できます。"
    },
    {
      id:"standard",
      label:"標準AI",
      minDays:145,
      score:65,
      className:"mode-standard",
      description:"1か月予測、精度検証、総合判断を標準設定で利用できます。"
    },
    {
      id:"advanced",
      label:"高精度AI",
      minDays:280,
      score:82,
      className:"mode-advanced",
      description:"1年程度の学習期間と統計モデルを安定して利用できます。"
    },
    {
      id:"full",
      label:"フルAI",
      minDays:550,
      score:100,
      className:"mode-full",
      description:"長期検証、局面比較、統計モデル、Adaptive AIを最大設定で利用できます。"
    }
  ];

  function detect(days){
    const available=MODES.filter(mode=>days>=mode.minDays);
    const current=available.at(-1)||{
      ...MODES[0],
      id:"limited",
      label:"準備モード",
      minDays:0,
      score:10,
      className:"mode-simple",
      description:"最低45営業日に達するまで、基本分析を中心に利用します。"
    };
    const currentIndex=MODES.findIndex(mode=>mode.id===current.id);
    const next=currentIndex>=0&&currentIndex<MODES.length-1
      ?MODES[currentIndex+1]
      :null;

    return {
      days,
      current,
      next,
      remaining:next?Math.max(next.minDays-days,0):0,
      progress:next
        ?clamp(
            (days-current.minDays)/
            Math.max(next.minDays-current.minDays,1)*100,
            0,
            100
          )
        :100
    };
  }

  function bestValidationSettings(days,requested={}){
    const requestedHorizon=+requested.horizon||21;
    const requestedLookback=+requested.lookback||120;
    const requestedStep=+requested.step||5;

    const candidates=[
      {horizon:126,lookback:504,step:21,min:651,label:"半年・504日"},
      {horizon:63,lookback:252,step:10,min:336,label:"3か月・252日"},
      {horizon:21,lookback:252,step:5,min:294,label:"1か月・252日"},
      {horizon:21,lookback:120,step:5,min:162,label:"1か月・120日"},
      {horizon:5,lookback:120,step:5,min:146,label:"1週間・120日"},
      {horizon:21,lookback:60,step:5,min:102,label:"1か月・60日"},
      {horizon:5,lookback:60,step:5,min:86,label:"1週間・60日"},
      {horizon:5,lookback:40,step:5,min:66,label:"簡易1週間・40日"}
    ];

    const requestedMin=Math.max(requestedLookback,63)+requestedHorizon+20;
    if(days>=requestedMin){
      return {
        horizon:requestedHorizon,
        lookback:requestedLookback,
        step:requestedStep,
        adjusted:false,
        minimum:requestedMin,
        label:"指定設定"
      };
    }

    const selected=candidates.find(candidate=>days>=candidate.min);
    if(selected){
      return {...selected,adjusted:true,minimum:selected.min};
    }

    return {
      horizon:Math.max(1,Math.min(5,days-41)),
      lookback:Math.max(30,Math.min(40,days-21)),
      step:5,
      adjusted:true,
      minimum:45,
      label:"超軽量推定",
      limited:true
    };
  }

  function bestAdvisorSettings(days,requestedHorizon=21){
    if(days>=550)return {horizon:requestedHorizon,lookback:252,mode:"full",adjusted:false};
    if(days>=280)return {horizon:Math.min(requestedHorizon,63),lookback:252,mode:"advanced",adjusted:requestedHorizon>63};
    if(days>=145)return {horizon:Math.min(requestedHorizon,21),lookback:120,mode:"standard",adjusted:requestedHorizon>21};
    if(days>=85)return {horizon:5,lookback:60,mode:"light",adjusted:true};
    return {horizon:Math.max(1,Math.min(5,days-41)),lookback:Math.max(30,days-21),mode:"simple",adjusted:true,limited:true};
  }

  function bestStatSettings(days,requested={}){
    if(days>=550)return {horizon:+requested.horizon||21,lookback:504,model:requested.model||"auto",adjusted:false};
    if(days>=280)return {horizon:Math.min(+requested.horizon||21,63),lookback:252,model:requested.model||"auto",adjusted:false};
    if(days>=145)return {horizon:Math.min(+requested.horizon||21,21),lookback:120,model:"ensemble",adjusted:true};
    if(days>=70)return {horizon:5,lookback:60,model:"baseline",adjusted:true};
    return {horizon:5,lookback:Math.max(30,days-10),model:"baseline",adjusted:true,limited:true};
  }

  function diagnose(days){
    const mode=detect(days);
    return {
      ...mode,
      validation:bestValidationSettings(days,{
        horizon:+$("measureHorizon")?.value||21,
        lookback:+$("measureLookback")?.value||120,
        step:+$("measureStep")?.value||5
      }),
      advisor:bestAdvisorSettings(
        days,
        +$("advisorHorizon")?.value||21
      ),
      statistics:bestStatSettings(days,{
        horizon:+$("statHorizon")?.value||21,
        model:$("statModel")?.value||"auto"
      })
    };
  }

  return Object.freeze({
    detect,
    diagnose,
    bestValidationSettings,
    bestAdvisorSettings,
    bestStatSettings,
    modes:()=>MODES.map(mode=>({...mode}))
  });
})();

function runAutoModeDiagnosis(){
  const status=$("autoModeStatus");
  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、「分析を開始」を押してください。";
    return;
  }

  const diagnosis=DataAdaptiveMode.diagnose(last.d.length);
  last.autoMode=diagnosis;
  applyAutoModeToControls(diagnosis);
  renderAutoMode(diagnosis);

  status.className="status ok";
  status.textContent=`${last.d.length}営業日を診断し、${diagnosis.current.label}を選択しました。`;
}

function applyAutoModeToControls(diagnosis){
  const validation=diagnosis.validation;
  if($("measureHorizon"))$("measureHorizon").value=String(validation.horizon);
  if($("measureLookback")){
    const option=[...$("measureLookback").options]
      .find(item=>+item.value===validation.lookback);
    if(option)$("measureLookback").value=String(validation.lookback);
  }
  if($("measureStep"))$("measureStep").value=String(validation.step);

  const advisor=diagnosis.advisor;
  if($("advisorHorizon")){
    const option=[...$("advisorHorizon").options]
      .find(item=>+item.value===advisor.horizon);
    if(option)$("advisorHorizon").value=String(advisor.horizon);
  }

  const statistics=diagnosis.statistics;
  if($("statHorizon")){
    const option=[...$("statHorizon").options]
      .find(item=>+item.value===statistics.horizon);
    if(option)$("statHorizon").value=String(statistics.horizon);
  }
  if($("statLookback")){
    const option=[...$("statLookback").options]
      .find(item=>+item.value===statistics.lookback);
    if(option)$("statLookback").value=String(statistics.lookback);
  }
  if($("statModel")){
    const option=[...$("statModel").options]
      .find(item=>item.value===statistics.model);
    if(option)$("statModel").value=statistics.model;
  }
}

function renderAutoMode(diagnosis){
  const {current,next,days,remaining,progress}=diagnosis;

  $("autoModeHero").innerHTML=`
    <div class="automode-name ${current.className}">${current.label}</div>
    <div class="automode-level">利用データ ${days}営業日</div>
    <div class="small" style="margin-top:8px">${current.description}</div>`;

  $("autoModeBar").innerHTML=`
    <div class="scorebar"><span style="width:${current.score}%"></span></div>`;

  $("autoModeComment").textContent=next
    ?`現在は${current.label}で動作します。

次の「${next.label}」まで、あと${remaining}営業日です。
現在のデータで利用可能な最大設定へ自動調整します。`
    :`フルAIを利用できます。長期検証と高精度設定を自動採用します。`;

  const rows=[
    {
      feature:"予測精度測定",
      setting:`${diagnosis.validation.horizon}日予測・${diagnosis.validation.lookback}日学習`,
      adjusted:diagnosis.validation.adjusted
    },
    {
      feature:"AI総合判断",
      setting:`${diagnosis.advisor.horizon}日予測・${diagnosis.advisor.lookback}日学習`,
      adjusted:diagnosis.advisor.adjusted
    },
    {
      feature:"統計モデル",
      setting:`${diagnosis.statistics.horizon}日予測・${diagnosis.statistics.lookback}日学習・${statModelLabel(diagnosis.statistics.model)}`,
      adjusted:diagnosis.statistics.adjusted
    }
  ];

  $("autoModeTable").innerHTML=`
    <div class="tablewrap"><table>
      <thead><tr><th>機能</th><th>自動設定</th><th>状態</th></tr></thead>
      <tbody>${rows.map(row=>`
        <tr>
          <td>${row.feature}</td>
          <td>${row.setting}</td>
          <td class="${row.adjusted?"mode-adjusted":"mode-ok"}">
            ${row.adjusted?"自動調整":"指定設定"}
          </td>
        </tr>`).join("")}</tbody>
    </table></div>`;

  $("autoModeAdvice").textContent=`エラーで停止する代わりに、現在のデータ量で実行可能な設定へ自動変更します。

データが増えると、軽量AI → 標準AI → 高精度AI → フルAIへ自動移行します。`;

  $("autoModeProgressCards").innerHTML=next
    ?`<div class="card">
        <div class="card-title">次のモード</div>
        <div class="card-value">${next.label}</div>
      </div>
      <div class="card">
        <div class="card-title">不足日数</div>
        <div class="card-value">${remaining}営業日</div>
      </div>
      <div class="card">
        <div class="card-title">進捗</div>
        <div class="card-value">${progress.toFixed(0)}%</div>
      </div>`
    :`<div class="card">
        <div class="card-title">モード</div>
        <div class="card-value">最高設定</div>
      </div>`;
}





/* =========================================================
   Ver.23 Scenario AI
   ========================================================= */

const ScenarioAIEngine=(()=>{
  function softmax(values){
    const maxValue=Math.max(...values);
    const expValues=values.map(value=>Math.exp(value-maxValue));
    const total=expValues.reduce((sum,value)=>sum+value,0)||1;
    return expValues.map(value=>value/total);
  }

  function calculateProbabilities({
    latest,
    center,
    low,
    high,
    regime,
    confidence,
    annualizedVol
  }){
    const centerReturn=(center/latest-1)*100;
    const upside=(high/latest-1)*100;
    const downside=(low/latest-1)*100;

    let bullScore=centerReturn*.35+upside*.08;
    let baseScore=3-Math.abs(centerReturn)*.18;
    let bearScore=-centerReturn*.35+Math.abs(downside)*.08;

    if(regime==="bull"){
      bullScore+=1.2;
      bearScore-=.4;
    }else if(regime==="bear"){
      bearScore+=1.2;
      bullScore-=.4;
    }else if(regime==="volatile"){
      bearScore+=.5;
      bullScore+=.3;
      baseScore-=.6;
    }else{
      baseScore+=.5;
    }

    const volPenalty=Math.max(annualizedVol-25,0)/20;
    baseScore-=volPenalty;
    bearScore+=volPenalty*.45;
    bullScore+=volPenalty*.15;

    const confidenceBoost=(confidence-50)/100;
    if(centerReturn>=0)bullScore+=confidenceBoost;
    else bearScore+=confidenceBoost;

    const [bull,base,bear]=softmax([bullScore,baseScore,bearScore]);

    return {
      bull:bull*100,
      base:base*100,
      bear:bear*100
    };
  }

  function actionAdvice({probabilities,centerReturn,lossProbability,regime}){
    const bull=probabilities.bull;
    const bear=probabilities.bear;

    let accumulation;
    let lumpSum;
    let warning;

    if(bear>=45||lossProbability>=45||regime==="bear"){
      accumulation="積立継続は可能ですが、無理な増額は避ける判断です。";
      lumpSum="一括投資は見送り、複数回に分ける方が安全です。";
      warning="高";
    }else if(bull>=45&&centerReturn>1){
      accumulation="通常積立の継続が適しています。";
      lumpSum="追加投資は一括ではなく、2〜4回に分ける判断が適しています。";
      warning="低〜中";
    }else{
      accumulation="通常積立を維持し、相場の方向確認を待つ判断です。";
      lumpSum="一括投資は急がず、少額の分割投資が適しています。";
      warning="中";
    }

    return {accumulation,lumpSum,warning};
  }

  function generateComment({
    probabilities,
    selectedModel,
    horizon,
    latest,
    center,
    low,
    high,
    regime,
    confidence,
    annualizedVol,
    lossProbability
  }){
    const centerReturn=(center/latest-1)*100;
    const advice=actionAdvice({
      probabilities,
      centerReturn,
      lossProbability,
      regime
    });

    const dominant=Object.entries(probabilities)
      .sort((a,b)=>b[1]-a[1])[0];

    const dominantLabel={
      bull:"強気",
      base:"横ばい・基準",
      bear:"弱気"
    }[dominant[0]];

    let interpretation;
    if(dominant[0]==="bull"){
      interpretation="上昇シナリオが最も優勢ですが、予測上限だけを前提にしないことが重要です。";
    }else if(dominant[0]==="bear"){
      interpretation="下落シナリオへの警戒が必要で、資金管理を優先すべき局面です。";
    }else{
      interpretation="方向感が弱く、上昇・下落のどちらにも動き得る局面です。";
    }

    return `WCM AI分析

最有力シナリオ：
${dominantLabel} ${dominant[1].toFixed(1)}%

予測期間：
${horizon}営業日

選択モデル：
${selectedModel}

現在基準価額：
${Math.round(latest).toLocaleString()}円

中心予測：
${Math.round(center).toLocaleString()}円
（${centerReturn>=0?"+":""}${centerReturn.toFixed(2)}%）

予測範囲：
${Math.round(low).toLocaleString()}円 〜 ${Math.round(high).toLocaleString()}円

現在の相場局面：
${regimeLabel(regime)}

AI信頼度：
${confidence.toFixed(0)}点

年率ボラティリティ：
${annualizedVol.toFixed(1)}%

${interpretation}

積立判断：
${advice.accumulation}

一括投資判断：
${advice.lumpSum}

警戒度：
${advice.warning}

このコメントは過去データに基づく参考情報で、将来の成果を保証するものではありません。`;
  }

  return Object.freeze({
    calculateProbabilities,
    generateComment
  });
})();

function estimateScenarioLossProbability(latest,center,low){
  if(latest<=0)return 50;
  const centerReturn=(center/latest-1)*100;
  const lowReturn=(low/latest-1)*100;
  return clamp(
    35-centerReturn*2.5+Math.abs(Math.min(lowReturn,0))*.6,
    2,
    95
  );
}

const AutoDataService=(()=>{
  const paths={
    dist:"./wcm_distribution.csv",
    growth:"./wcm_growth.csv",
    meta:"./update-info.json"
  };

  async function fetchBuffer(path){
    const response=await fetch(
      `${path}?t=${Date.now()}`,
      {cache:"no-store"}
    );

    if(!response.ok){
      throw new Error(`${path}: ${response.status} ${response.statusText}`);
    }

    return response.arrayBuffer();
  }

  async function loadCsv(path){
    const buffer=await fetchBuffer(path);
    const rows=parse(decode(buffer));

    if(rows.length<10){
      throw new Error(`${path}: 有効な基準価額データが不足しています。`);
    }

    return rows;
  }

  async function loadMeta(){
    try{
      const response=await fetch(
        `${paths.meta}?t=${Date.now()}`,
        {cache:"no-store"}
      );
      return response.ok?response.json():null;
    }catch{
      return null;
    }
  }

  async function load(){
    const [distRows,growthRows,meta]=await Promise.all([
      loadCsv(paths.dist),
      loadCsv(paths.growth),
      loadMeta()
    ]);

    return {
      dist:{
        rows:distRows,
        source:"root-file",
        label:"予想分配金提示型",
        savedAt:meta?.updated_at||null,
        latestDate:meta?.funds?.distribution?.latest_date||null
      },
      growth:{
        rows:growthRows,
        source:"root-file",
        label:"資産成長型",
        savedAt:meta?.updated_at||null,
        latestDate:meta?.funds?.growth?.latest_date||null
      },
      meta
    };
  }

  return Object.freeze({load,paths});
})();


function prepareLoadedData(distRows,growthRows,sourceLabel,sourceDetails=null){
  distData=distRows;
  growthData=growthRows;
  last.autoDataSources=sourceDetails;
  const start=new Date(Math.max(distData[0].date,growthData[0].date));
  if(!$("startDate").value)$("startDate").value=fmt(start).replaceAll("/","-");
  $("distStatus").className="status ok";
  $("distStatus").textContent=`${sourceLabel}：${distData.length.toLocaleString()}件`;
  $("growthStatus").className="status ok";
  $("growthStatus").textContent=`${sourceLabel}：${growthData.length.toLocaleString()}件`;
  $("analyze").disabled=false;
  $("analyzeAutoData").disabled=false;
  $("mainStatus").textContent="分析できます。";
}

async function loadAutomaticCsv({silent=false}={}){
  const status=$("autoDataStatus");

  if(!silent){
    status.className="status";
    status.textContent="リポジトリ直下のCSVを読み込んでいます…";
  }

  try{
    const data=await AutoDataService.load();

    prepareLoadedData(
      data.dist.rows,
      data.growth.rows,
      "ルート保存CSV",
      {
        dist:data.dist,
        growth:data.growth
      }
    );

    const latestDist=data.dist.rows.at(-1);
    const latestGrowth=data.growth.rows.at(-1);
    const updated=data.meta?.updated_at_jst||
      data.meta?.updated_at||
      "CSV内の最新日を使用";

    status.className="status ok";
    status.innerHTML=
      '<span class="auto-data-ready">保存済みCSVを読み込みました。</span>';

    $("autoDataMeta").textContent=
      `最終更新：${updated} ／ `+
      `予想分配型：${latestDist.dateText}・${latestDist.nav.toLocaleString()}円 ／ `+
      `資産成長型：${latestGrowth.dateText}・${latestGrowth.nav.toLocaleString()}円`;

    renderAutoDataSources(data);
    return true;
  }catch(error){
    console.warn("自動CSV読込失敗",error);

    status.className="status bad";
    status.innerHTML=
      '<span class="auto-data-error">保存済みCSVを読み込めませんでした。</span> '+
      'GitHubの一番上に2つのCSVを置くか、下の手動CSVを選択してください。';

    $("autoDataMeta").textContent=`原因：${error.message}`;
    renderAutoDataSources(null,error);
    return false;
  }
}


function renderAutoDataSources(data,error=null){
  const container=$("autoDataSourceCards");
  if(!container)return;

  if(!data){
    container.innerHTML=`
      <div class="card source-card-manual">
        <div class="card-title">現在の読込方法</div>
        <div class="card-value">手動CSV</div>
        <span class="source-badge source-manual">フォールバック</span>
        <div class="card-sub">${error?.message||"自動更新CSVがありません"}</div>
      </div>`;
    return;
  }

  function sourceCard(item){
    const saved=item.savedAt
      ?new Date(item.savedAt).toLocaleString("ja-JP")
      :"不明";

    return `
      <div class="card source-card-live">
        <div class="card-title">${item.label}</div>
        <div class="card-value">ルート保存CSV</div>
        <span class="source-badge source-live">自動読込</span>
        <div class="card-sub">更新日時：${saved}</div>
      </div>`;
  }

  container.innerHTML=
    sourceCard(data.dist)+sourceCard(data.growth);
}


async function analyzeAutomaticCsv(){
  const loaded=distData&&growthData?true:await loadAutomaticCsv();
  if(loaded)$("analyze").click();
}

function addBusinessDays(dateValue,count){
  const value=new Date(dateValue);
  let left=count;
  while(left>0){
    value.setDate(value.getDate()+1);
    const day=value.getDay();
    if(day!==0&&day!==6)left-=1;
  }
  return value;
}

function buildFuturePath(rows,horizon,modelChoice){
  const settings=DataAdaptiveMode.bestStatSettings(rows.length,{horizon,model:modelChoice});
  const result=StatisticalForecastEngine.run(rows,{
    horizon:settings.horizon,
    lookback:settings.lookback,
    model:modelChoice,
    interval:.90
  });
  const selected=result.selected;
  const latest=rows.at(-1).nav;
  const centerLog=Math.log(selected.center/latest);
  const lowLog=Math.log(selected.low/latest);
  const highLog=Math.log(selected.high/latest);
  const center=[],low=[],high=[],dates=[];
  for(let step=0;step<=result.horizon;step++){
    const fraction=result.horizon?step/result.horizon:0;
    const sqrtFraction=Math.sqrt(fraction);
    const centerValue=latest*Math.exp(centerLog*fraction);
    center.push(centerValue);
    low.push(centerValue*Math.exp(-(centerLog-lowLog)*sqrtFraction));
    high.push(centerValue*Math.exp((highLog-centerLog)*sqrtFraction));
    dates.push(fmt(step===0?rows.at(-1).date:addBusinessDays(rows.at(-1).date,step)));
  }
  return {...result,centerPath:center,lowPath:low,highPath:high,dates};
}

function renderFutureNavChart(){
  const status=$("futureChartStatus");
  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、分析を開始してください。";
    return;
  }
  status.className="status";
  status.textContent="将来の予測経路を計算しています…";
  try{
    const prediction=buildFuturePath(
      last.d,
      +$("futureChartHorizon").value||21,
      $("futureChartModel").value||"auto"
    );
    last.statistics=prediction;
    const historyDays=+$("futureHistoryDays").value||126;
    drawFutureForecastChart(
      $("futureNavChart"),
      last.d.slice(-Math.min(historyDays,last.d.length)),
      prediction
    );
    const selected=prediction.selected;
    const latest=last.d.at(-1).nav;
    const rate=(selected.center/latest-1)*100;
    $("futureChartLegend").innerHTML=`
      <span><i style="background:#0f172a"></i>実績</span>
      <span><i style="background:#2563eb"></i>中心予測</span>
      <span><i style="background:#16a34a"></i>予測上限</span>
      <span><i style="background:#dc2626"></i>予測下限</span>
      <span><i style="background:rgba(37,99,235,.18)"></i>90%予測範囲</span>`;
    $("futureChartComment").textContent=`選択モデル：${statModelLabel(prediction.selectedId)}
予測期間：${prediction.horizon}営業日
現在基準価額：${Math.round(latest).toLocaleString()}円
中心予測：${Math.round(selected.center).toLocaleString()}円（${rate>=0?"+":""}${rate.toFixed(2)}%）
90%予測範囲：${Math.round(selected.low).toLocaleString()}円〜${Math.round(selected.high).toLocaleString()}円

将来経路は最終予測値と予測範囲を日次へ展開した参考シナリオです。`;

    const confidence=last.advisor?.advisor?.confidence||
      last.measurement?.integratedMetrics?.score||
      55;

    const probabilities=ScenarioAIEngine.calculateProbabilities({
      latest,
      center:selected.center,
      low:selected.low,
      high:selected.high,
      regime:prediction.regime,
      confidence,
      annualizedVol:prediction.diagnostics?.annualizedVol||selected.annualizedVol||25
    });

    $("scenarioProbabilityCards").innerHTML=`
      <div class="card scenario-bull">
        <div class="card-title">強気シナリオ</div>
        <div class="scenario-probability scenario-positive">${probabilities.bull.toFixed(1)}%</div>
        <div class="card-sub">${Math.round(selected.high).toLocaleString()}円付近</div>
      </div>
      <div class="card scenario-base">
        <div class="card-title">基準シナリオ</div>
        <div class="scenario-probability scenario-neutral">${probabilities.base.toFixed(1)}%</div>
        <div class="card-sub">${Math.round(selected.center).toLocaleString()}円付近</div>
      </div>
      <div class="card scenario-bear">
        <div class="card-title">弱気シナリオ</div>
        <div class="scenario-probability scenario-negative">${probabilities.bear.toFixed(1)}%</div>
        <div class="card-sub">${Math.round(selected.low).toLocaleString()}円付近</div>
      </div>`;

    const lossProbability=estimateScenarioLossProbability(
      latest,
      selected.center,
      selected.low
    );

    $("scenarioAiComment").textContent=ScenarioAIEngine.generateComment({
      probabilities,
      selectedModel:statModelLabel(prediction.selectedId),
      horizon:prediction.horizon,
      latest,
      center:selected.center,
      low:selected.low,
      high:selected.high,
      regime:prediction.regime,
      confidence,
      annualizedVol:prediction.diagnostics?.annualizedVol||selected.annualizedVol||25,
      lossProbability
    });
    status.className="status ok";
    status.textContent="予想チャートを更新しました。";
  }catch(error){
    console.error(error);
    status.className="status bad";
    status.textContent=`予想チャートエラー：${error.message}`;
  }
}

function drawFutureForecastChart(element,history,prediction){
  const width=820,height=350,left=58,right=24,top=28,bottom=46;
  const historical=history.map(row=>row.nav);
  const all=[...historical,...prediction.lowPath,...prediction.highPath].filter(Number.isFinite);
  let min=Math.min(...all),max=Math.max(...all);
  const pad=(max-min||1)*.10;
  min-=pad; max+=pad;
  const span=max-min||1;
  const total=history.length+prediction.centerPath.length-1;
  const x=index=>left+index*(width-left-right)/Math.max(total-1,1);
  const y=value=>top+(max-value)*(height-top-bottom)/span;
  const points=(values,offset=0)=>values.map((value,index)=>`${x(offset+index)},${y(value)}`).join(" ");
  const offset=history.length-1;
  const band=[
    ...prediction.highPath.map((value,index)=>`${x(offset+index)},${y(value)}`),
    ...prediction.lowPath.slice().reverse().map((value,index)=>`${x(offset+prediction.lowPath.length-1-index)},${y(value)}`)
  ].join(" ");
  const grid=[];
  for(let line=0;line<=4;line++){
    const value=max-span*line/4;
    const yy=top+(height-top-bottom)*line/4;
    grid.push(`<line x1="${left}" y1="${yy}" x2="${width-right}" y2="${yy}" stroke="#cbd5e1"/>`);
    grid.push(`<text x="${left-8}" y="${yy+4}" text-anchor="end" fill="#475569" font-size="11">${Math.round(value).toLocaleString()}</text>`);
  }
  const split=x(offset);
  element.innerHTML=`<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="実績基準価額と将来予測範囲">
    <rect width="${width}" height="${height}" fill="#f8fafc"/>
    ${grid.join("")}
    <polygon points="${band}" fill="rgba(37,99,235,.14)"/>
    <polyline points="${points(historical)}" fill="none" stroke="#0f172a" stroke-width="3"/>
    <polyline points="${points(prediction.centerPath,offset)}" fill="none" stroke="#2563eb" stroke-width="3"/>
    <polyline points="${points(prediction.highPath,offset)}" fill="none" stroke="#16a34a" stroke-width="2" stroke-dasharray="7 5"/>
    <polyline points="${points(prediction.lowPath,offset)}" fill="none" stroke="#dc2626" stroke-width="2" stroke-dasharray="7 5"/>
    <line x1="${split}" y1="${top}" x2="${split}" y2="${height-bottom}" stroke="#7c3aed" stroke-width="2" stroke-dasharray="4 5"/>
    <text x="${split+6}" y="${top+14}" fill="#6d28d9" font-size="11">予測開始</text>
    <text x="${left}" y="${height-14}" fill="#475569" font-size="11">${history[0].dateText}</text>
    <text x="${split}" y="${height-14}" text-anchor="middle" fill="#475569" font-size="11">${history.at(-1).dateText}</text>
    <text x="${width-right}" y="${height-14}" text-anchor="end" fill="#475569" font-size="11">${prediction.dates.at(-1)}</text>
  </svg>`;
}


/* =========================================================
   Ver.24 Self Learning AI
   ========================================================= */

const SelfLearningAI=(()=>{
  const STORAGE_KEY="wcm24-self-learning-v1";
  const MODEL_IDS=["garch","student-t","regime","ensemble","baseline"];
  const LABELS={
    garch:"GARCH風",
    "student-t":"t分布",
    regime:"レジーム切替",
    ensemble:"精度加重アンサンブル",
    baseline:"従来アンサンブル"
  };

  function emptyState(){
    return {
      version:1,
      predictions:[],
      weights:Object.fromEntries(MODEL_IDS.map(id=>[id,1/MODEL_IDS.length])),
      modelStats:{},
      byRegime:{},
      byHorizon:{},
      confidence:0,
      updatedAt:null
    };
  }

  function load(){
    try{
      const parsed=JSON.parse(localStorage.getItem(STORAGE_KEY)||"null");
      if(parsed&&parsed.version===1)return parsed;
    }catch(error){
      console.warn("自己学習データ読込失敗",error);
    }
    return emptyState();
  }

  function save(state){
    localStorage.setItem(STORAGE_KEY,JSON.stringify(state));
  }

  function reset(){
    localStorage.removeItem(STORAGE_KEY);
  }

  function normalize(raw){
    const total=Object.values(raw).reduce(
      (sum,value)=>sum+Math.max(value,0),
      0
    )||1;
    return Object.fromEntries(
      Object.entries(raw).map(([key,value])=>[
        key,
        Math.max(value,0)/total
      ])
    );
  }

  function currentForecastSnapshot(){
    if(!last.d||!last.statistics){
      throw new Error("先に将来予測チャートを作成してください。");
    }

    const statistics=last.statistics;
    const latestRow=last.d.at(-1);
    const horizon=statistics.horizon;
    const regime=statistics.regime||"unknown";

    const modelForecasts={};
    for(const model of statistics.models||[]){
      modelForecasts[model.id]={
        center:model.center,
        low:model.low,
        high:model.high
      };
    }

    return {
      id:`sl-${Date.now()}-${Math.random().toString(36).slice(2,8)}`,
      createdAt:new Date().toISOString(),
      originDate:latestRow.dateText,
      originDateValue:latestRow.date instanceof Date
        ?latestRow.date.toISOString()
        :String(latestRow.date||""),
      originNav:latestRow.nav,
      horizon,
      regime,
      selectedModel:statistics.selectedId,
      integratedCenter:statistics.selected.center,
      integratedLow:statistics.selected.low,
      integratedHigh:statistics.selected.high,
      modelForecasts,
      evaluated:false,
      actualDate:null,
      actualNav:null,
      modelResults:null
    };
  }

  function addPrediction(snapshot){
    const state=load();
    state.predictions.unshift(snapshot);
    state.predictions=state.predictions.slice(0,120);
    save(state);
    return state;
  }

  function findOriginIndex(rows,prediction){
    return rows.findIndex(row=>{
      if(row.dateText===prediction.originDate)return true;
      const value=row.date instanceof Date
        ?row.date.toISOString()
        :String(row.date||"");
      return value===prediction.originDateValue;
    });
  }

  function evaluatePrediction(prediction,rows){
    if(prediction.evaluated)return prediction;

    const originIndex=findOriginIndex(rows,prediction);
    if(originIndex<0)return prediction;

    const targetIndex=originIndex+prediction.horizon;
    if(targetIndex>=rows.length)return prediction;

    const actualRow=rows[targetIndex];
    const actualDirection=Math.sign(actualRow.nav-prediction.originNav);
    const modelResults={};

    for(const [modelId,forecast] of Object.entries(
      prediction.modelForecasts||{}
    )){
      const errorPct=Math.abs(forecast.center-actualRow.nav)/actualRow.nav*100;
      const signedErrorPct=(forecast.center-actualRow.nav)/actualRow.nav*100;
      const predictedDirection=Math.sign(
        forecast.center-prediction.originNav
      );

      modelResults[modelId]={
        errorPct,
        signedErrorPct,
        directionCorrect:predictedDirection===actualDirection,
        intervalHit:
          actualRow.nav>=forecast.low&&
          actualRow.nav<=forecast.high
      };
    }

    return {
      ...prediction,
      evaluated:true,
      actualDate:actualRow.dateText,
      actualNav:actualRow.nav,
      modelResults
    };
  }

  function recencyWeight(index,total,decay=.96){
    const age=Math.max(total-index-1,0);
    return Math.pow(decay,age);
  }

  function resultScore(result){
    const errorComponent=1/Math.max(result.errorPct,.5)**2;
    const directionBonus=result.directionCorrect?1.35:.65;
    const intervalBonus=result.intervalHit?1.10:.90;
    return errorComponent*directionBonus*intervalBonus;
  }

  function aggregateStats(predictions){
    const evaluated=predictions
      .filter(item=>item.evaluated)
      .sort((a,b)=>String(a.actualDate).localeCompare(String(b.actualDate)));

    const buckets=Object.fromEntries(
      MODEL_IDS.map(id=>[id,{
        id,
        label:LABELS[id],
        count:0,
        weightedScore:0,
        errors:[],
        signedErrors:[],
        directionHits:0,
        intervalHits:0,
        weightTotal:0
      }])
    );

    evaluated.forEach((prediction,index)=>{
      const weight=recencyWeight(index,evaluated.length);
      for(const [modelId,result] of Object.entries(
        prediction.modelResults||{}
      )){
        if(!buckets[modelId])continue;
        const bucket=buckets[modelId];
        bucket.count+=1;
        bucket.weightedScore+=resultScore(result)*weight;
        bucket.weightTotal+=weight;
        bucket.errors.push(result.errorPct);
        bucket.signedErrors.push(result.signedErrorPct);
        if(result.directionCorrect)bucket.directionHits+=1;
        if(result.intervalHit)bucket.intervalHits+=1;
      }
    });

    return Object.values(buckets).map(bucket=>{
      const mape=bucket.count?mean(bucket.errors):0;
      const bias=bucket.count?mean(bucket.signedErrors):0;
      const directionHit=bucket.count
        ?bucket.directionHits/bucket.count*100
        :0;
      const intervalCoverage=bucket.count
        ?bucket.intervalHits/bucket.count*100
        :0;
      const adaptiveScore=bucket.weightTotal
        ?bucket.weightedScore/bucket.weightTotal
        :0;

      return {
        id:bucket.id,
        label:bucket.label,
        count:bucket.count,
        mape,
        bias,
        directionHit,
        intervalCoverage,
        adaptiveScore
      };
    });
  }

  function weightsFromStats(stats){
    const raw={};
    for(const stat of stats){
      raw[stat.id]=stat.count
        ?Math.max(stat.adaptiveScore,.0001)
        :.0001;
    }
    return normalize(raw);
  }

  function groupedWeights(predictions,keyGetter,globalWeights){
    const groups={};

    for(const prediction of predictions.filter(item=>item.evaluated)){
      const key=String(keyGetter(prediction));
      (groups[key]??=[]).push(prediction);
    }

    const result={};

    for(const [key,items] of Object.entries(groups)){
      const stats=aggregateStats(items);
      const local=weightsFromStats(stats);
      const strength=clamp(items.length/20,0,1);
      const blended={};

      for(const modelId of MODEL_IDS){
        blended[modelId]=
          (local[modelId]||0)*strength+
          (globalWeights[modelId]||0)*(1-strength);
      }

      result[key]={
        count:items.length,
        weights:normalize(blended)
      };
    }

    return result;
  }

  function confidence(predictions,weights){
    const evaluated=predictions.filter(item=>item.evaluated);
    const sampleScore=clamp(evaluated.length/40,0,1);
    const maxWeight=Math.max(...Object.values(weights));
    const concentration=clamp((maxWeight-.20)/.45,0,1);
    return clamp(
      (sampleScore*.75+concentration*.25)*100,
      0,
      100
    );
  }

  function rebuild(rows){
    const state=load();
    const predictions=state.predictions.map(item=>
      evaluatePrediction(item,rows)
    );
    const stats=aggregateStats(predictions);
    const weights=weightsFromStats(stats);
    const byRegime=groupedWeights(
      predictions,
      item=>item.regime||"unknown",
      weights
    );
    const byHorizon=groupedWeights(
      predictions,
      item=>item.horizon||21,
      weights
    );

    const next={
      ...state,
      predictions,
      weights,
      modelStats:Object.fromEntries(stats.map(item=>[item.id,item])),
      byRegime,
      byHorizon,
      confidence:confidence(predictions,weights),
      updatedAt:new Date().toISOString()
    };

    save(next);
    return next;
  }

  function effectiveWeights(regime,horizon){
    const state=load();
    let weights={...state.weights};

    const regimeData=state.byRegime?.[String(regime)];
    if(regimeData){
      const strength=clamp(regimeData.count/20,0,1);
      for(const id of MODEL_IDS){
        weights[id]=
          (regimeData.weights[id]||0)*strength+
          (weights[id]||0)*(1-strength);
      }
      weights=normalize(weights);
    }

    const horizonData=state.byHorizon?.[String(horizon)];
    if(horizonData){
      const strength=clamp(horizonData.count/20,0,1);
      for(const id of MODEL_IDS){
        weights[id]=
          (horizonData.weights[id]||0)*strength+
          (weights[id]||0)*(1-strength);
      }
      weights=normalize(weights);
    }

    return weights;
  }

  return Object.freeze({
    load,
    save,
    reset,
    currentForecastSnapshot,
    addPrediction,
    rebuild,
    effectiveWeights,
    labels:()=>({...LABELS})
  });
})();

function saveCurrentLearningPrediction(){
  const status=$("selfLearningStatus");

  try{
    const snapshot=SelfLearningAI.currentForecastSnapshot();
    const state=SelfLearningAI.addPrediction(snapshot);
    renderSelfLearning(state);

    status.className="status ok";
    status.textContent=
      `${snapshot.horizon}営業日後の予測を学習用に保存しました。`;
  }catch(error){
    status.className="status bad";
    status.textContent=`保存エラー：${error.message}`;
  }
}

function evaluateSelfLearningPredictions(){
  const status=$("selfLearningStatus");

  if(!last.d){
    status.className="status bad";
    status.textContent="先にCSVを読み込み、分析を開始してください。";
    return;
  }

  try{
    const before=SelfLearningAI.load().predictions
      .filter(item=>item.evaluated).length;
    const state=SelfLearningAI.rebuild(last.d);
    const after=state.predictions.filter(item=>item.evaluated).length;
    const newlyEvaluated=after-before;

    renderSelfLearning(state);

    status.className="status ok";
    status.textContent=newlyEvaluated>0
      ?`${newlyEvaluated}件の予測を新しく実績照合しました。`
      :"新しく照合できる予測はありませんでした。";
  }catch(error){
    status.className="status bad";
    status.textContent=`実績照合エラー：${error.message}`;
  }
}

function resetSelfLearningData(){
  if(!confirm("自己学習データをすべて初期化しますか？"))return;

  SelfLearningAI.reset();
  const state=SelfLearningAI.load();
  renderSelfLearning(state);

  $("selfLearningStatus").className="status";
  $("selfLearningStatus").textContent="自己学習データを初期化しました。";
}

function renderSelfLearning(state=null){
  const current=state||SelfLearningAI.load();
  const labels=SelfLearningAI.labels();
  const evaluated=current.predictions.filter(item=>item.evaluated);
  const pending=current.predictions.filter(item=>!item.evaluated);
  const sortedWeights=Object.entries(current.weights||{})
    .sort((a,b)=>b[1]-a[1]);
  const top=sortedWeights[0]||["ensemble",.2];

  let stateLabel;
  if(current.confidence>=80)stateLabel="十分に学習";
  else if(current.confidence>=55)stateLabel="学習中";
  else if(current.confidence>0)stateLabel="初期学習";
  else stateLabel="未学習";

  $("selfLearningHero").innerHTML=`
    <div class="selflearning-score">${current.confidence.toFixed(0)}点</div>
    <div class="selflearning-state">AI信頼度・${stateLabel}</div>
    <div class="small" style="margin-top:8px">
      実績照合済み ${evaluated.length}件 ／ 未到来 ${pending.length}件
    </div>`;

  $("selfLearningConfidenceBar").innerHTML=`
    <div class="scorebar">
      <span style="width:${current.confidence}%"></span>
    </div>`;

  $("selfLearningSummary").textContent=evaluated.length
    ?`現在最も重視しているモデル：
${labels[top[0]]||top[0]}
重み ${(top[1]*100).toFixed(1)}%

最近の予測成績を強く反映し、相場局面と予測期間に応じて実効重みを変化させます。`
    :"まだ実績照合済み予測がありません。将来予測を保存し、予測期間経過後に最新CSVで照合してください。";

  $("selfLearningWeights").innerHTML=sortedWeights.map(
    ([id,weight])=>`
      <div class="weight-row">
        <span>${labels[id]||id}</span>
        <div class="weight-bar">
          <span style="width:${weight*100}%"></span>
        </div>
        <strong>${(weight*100).toFixed(1)}%</strong>
      </div>`
  ).join("");

  const stats=Object.values(current.modelStats||{})
    .sort((a,b)=>a.mape-b.mape);

  $("selfLearningModelTable").innerHTML=stats.length
    ?`<div class="tablewrap"><table>
      <thead>
        <tr>
          <th>モデル</th>
          <th>件数</th>
          <th>MAPE</th>
          <th>方向的中</th>
          <th>区間カバー</th>
          <th>偏り</th>
        </tr>
      </thead>
      <tbody>${stats.map(stat=>`
        <tr>
          <td>${stat.label}</td>
          <td>${stat.count}</td>
          <td>${stat.mape.toFixed(2)}%</td>
          <td>${stat.directionHit.toFixed(1)}%</td>
          <td>${stat.intervalCoverage.toFixed(1)}%</td>
          <td>${stat.bias>=0?"+":""}${stat.bias.toFixed(2)}%</td>
        </tr>`).join("")}
      </tbody>
    </table></div>`
    :'<div class="small">モデル成績はまだありません。</div>';

  const regimeRows=Object.entries(current.byRegime||{});
  $("selfLearningRegimeTable").innerHTML=regimeRows.length
    ?`<div class="tablewrap"><table>
      <thead><tr><th>相場局面</th><th>件数</th><th>最優秀モデル</th><th>重み</th></tr></thead>
      <tbody>${regimeRows.map(([regime,data])=>{
        const best=Object.entries(data.weights)
          .sort((a,b)=>b[1]-a[1])[0];
        return `<tr>
          <td>${regimeLabel(regime)}</td>
          <td>${data.count}</td>
          <td>${labels[best[0]]||best[0]}</td>
          <td>${(best[1]*100).toFixed(1)}%</td>
        </tr>`;
      }).join("")}</tbody>
    </table></div>`
    :'<div class="small">局面別学習データはまだありません。</div>';

  const horizonRows=Object.entries(current.byHorizon||{});
  $("selfLearningHorizonTable").innerHTML=horizonRows.length
    ?`<div class="tablewrap"><table>
      <thead><tr><th>予測期間</th><th>件数</th><th>最優秀モデル</th><th>重み</th></tr></thead>
      <tbody>${horizonRows.map(([horizon,data])=>{
        const best=Object.entries(data.weights)
          .sort((a,b)=>b[1]-a[1])[0];
        return `<tr>
          <td>${horizon}営業日</td>
          <td>${data.count}</td>
          <td>${labels[best[0]]||best[0]}</td>
          <td>${(best[1]*100).toFixed(1)}%</td>
        </tr>`;
      }).join("")}</tbody>
    </table></div>`
    :'<div class="small">期間別学習データはまだありません。</div>';

  $("selfLearningHistory").innerHTML=current.predictions.length
    ?current.predictions.map(item=>`
      <div class="learning-history-item">
        <div class="learning-history-head">
          <span>${item.originDate} → ${item.horizon}営業日後</span>
          <span>${item.evaluated?"照合済み":"未到来"}</span>
        </div>
        <div class="prediction-meta">
          選択モデル：${labels[item.selectedModel]||item.selectedModel}<br>
          中心予測：${Math.round(item.integratedCenter).toLocaleString()}円<br>
          ${item.evaluated
            ?`実績：${Math.round(item.actualNav).toLocaleString()}円（${item.actualDate}）`
            :"予測期間経過後に最新CSVで照合できます。"}
        </div>
      </div>`).join("")
    :'<div class="small">保存済み予測はありません。</div>';
}


/* =========================================================
   Ver.25 Integrated Investment Dashboard
   ========================================================= */

const V25DashboardEngine=(()=>{
  const MODEL_LABELS={
    garch:"GARCH風",
    "student-t":"t分布",
    regime:"レジーム切替",
    ensemble:"精度加重アンサンブル",
    baseline:"従来アンサンブル"
  };

  function getPurchasePlan(rows,initial,monthly,day,extraInvestments=[]){
    return plan(rows,initial,monthly,day,extraInvestments);
  }

  function simulateCostBasis(rows,config){
    const initial=Math.max(0,+config.initial||0);
    const monthly=Math.max(0,+config.monthly||0);
    const day=clamp(Math.round(+config.day||1),1,31);
    const taxRate=clamp(+config.taxRate||20.315,0,100)/100;
    const distributionMode=config.distributionMode||"reinvest";
    const purchases=getPurchasePlan(rows,initial,monthly,day,config.extraInvestments||[]);

    let units=0;
    let principal=0;
    let costBasis=0;
    let cashDistributions=0;
    let ordinaryGross=0;
    let specialGross=0;
    let taxPaid=0;
    const history=[];
    const distributions=[];

    for(const row of rows){
      const purchase=purchases.get(row.dateText)||0;

      if(purchase>0&&row.nav>0){
        const newUnits=purchase/row.nav*10000;
        units+=newUnits;
        principal+=purchase;
        costBasis+=purchase;
      }

      let ordinary=0;
      let special=0;
      let netDistribution=0;

      if(row.distribution>0&&units>0&&row.nav>0){
        const averageCostPer10000=costBasis/units*10000;
        const specialPer10000=clamp(
          averageCostPer10000-row.nav,
          0,
          row.distribution
        );
        const ordinaryPer10000=Math.max(
          row.distribution-specialPer10000,
          0
        );

        special=units*specialPer10000/10000;
        ordinary=units*ordinaryPer10000/10000;
        const ordinaryTax=ordinary*taxRate;
        taxPaid+=ordinaryTax;
        ordinaryGross+=ordinary;
        specialGross+=special;
        netDistribution=ordinary-ordinaryTax+special;

        // 特別分配相当額は個別元本を減額する推定
        costBasis=Math.max(costBasis-special,0);

        if(distributionMode==="reinvest"&&netDistribution>0){
          const reinvestedUnits=netDistribution/row.nav*10000;
          units+=reinvestedUnits;
          // 普通分配の再投資は新規取得、特別分配は元本払戻し再投資
          costBasis+=netDistribution;
        }else{
          cashDistributions+=netDistribution;
        }

        distributions.push({
          dateText:row.dateText,
          distributionPer10000:row.distribution,
          ordinary,
          special,
          tax:ordinaryTax,
          net:netDistribution,
          averageCostPer10000
        });
      }

      const marketValue=units*row.nav/10000;
      history.push({
        dateText:row.dateText,
        date:row.date,
        nav:row.nav,
        units,
        principal,
        costBasis,
        marketValue,
        cashDistributions,
        totalValue:marketValue+cashDistributions,
        ordinary,
        special
      });
    }

    let latest=history.at(-1)||{
      principal:0,costBasis:0,marketValue:0,cashDistributions:0,totalValue:0,units:0,nav:0
    };

    // Ver.27.5: 証券会社の現在値をアンカーとして優先できる。
    // 過去の積立・追加投資・分配履歴は分析用に再構築するが、
    // 現在評価額と現在の取得原価は実績値で上書きし、誤差の累積を将来へ持ち込まない。
    const actualMode=(config.actualMode||"estimated")==="actual";
    let actualAnchor=null;
    if(actualMode){
      const actualUnits=Math.max(0,Number(config.actualUnits)||0);
      const actualNav=Math.max(0,Number(config.actualNav)||0);
      const actualAvgCost=Math.max(0,Number(config.actualAvgCost)||0);
      let actualAcquisitionTotal=Math.max(0,Number(config.actualAcquisitionTotal)||0);
      if(actualAcquisitionTotal<=0&&actualUnits>0&&actualAvgCost>0){
        actualAcquisitionTotal=actualUnits*actualAvgCost/10000;
      }
      if(actualUnits>0&&actualNav>0){
        const actualMarketValue=actualUnits*actualNav/10000;
        const actualCostBasis=actualAcquisitionTotal>0
          ?actualAcquisitionTotal
          :(actualUnits>0&&actualAvgCost>0?actualUnits*actualAvgCost/10000:latest.costBasis);
        const actualDistributionTotal=Math.max(0,Number(config.actualDistributionTotal)||0);
        const actualOrdinaryDistribution=Math.max(0,Number(config.actualOrdinaryDistribution)||0);
        const actualSpecialDistribution=Math.max(0,Number(config.actualSpecialDistribution)||0);
        const actualTotalReturn=Number(config.actualTotalReturn)||0;
        actualAnchor={
          units:actualUnits,
          nav:actualNav,
          averageCostPer10000:actualAvgCost>0?actualAvgCost:(actualUnits>0?actualCostBasis/actualUnits*10000:0),
          acquisitionTotal:actualCostBasis,
          marketValue:actualMarketValue,
          distributionTotal:actualDistributionTotal,
          ordinaryDistribution:actualOrdinaryDistribution,
          specialDistribution:actualSpecialDistribution,
          totalReturn:actualTotalReturn,
          distributionBreakdownGap:actualDistributionTotal-(actualOrdinaryDistribution+actualSpecialDistribution),
          estimatedMarketValue:latest.marketValue,
          estimatedUnits:latest.units,
          estimatedCostBasis:latest.costBasis,
          estimatedOrdinaryDistribution:ordinaryGross,
          estimatedSpecialDistribution:specialGross,
          estimatedDistributionTotal:ordinaryGross+specialGross
        };
        latest={
          ...latest,
          units:actualUnits,
          nav:actualNav,
          costBasis:actualCostBasis,
          marketValue:actualMarketValue,
          totalValue:actualMarketValue+latest.cashDistributions,
          actualAnchored:true
        };
        if(history.length)history[history.length-1]={...history[history.length-1],...latest};
      }
    }

    return {
      history,
      distributions,
      latest,
      actualAnchor,
      ordinaryGross,
      specialGross,
      taxPaid,
      distributionMode
    };
  }

  function multiHorizonForecast(rows){
    const horizons=[5,21,63,126];
    return horizons.map(horizon=>{
      const settings=DataAdaptiveMode.bestStatSettings(
        rows.length,
        {horizon,model:"auto"}
      );
      const result=StatisticalForecastEngine.run(rows,{
        horizon:settings.horizon,
        lookback:settings.lookback,
        model:"auto",
        interval:.90
      });
      const latest=rows.at(-1).nav;
      return {
        requestedHorizon:horizon,
        horizon:result.horizon,
        label:{
          5:"1週間",
          21:"1か月",
          63:"3か月",
          126:"6か月"
        }[horizon],
        center:result.selected.center,
        low:result.selected.low,
        high:result.selected.high,
        returnRate:(result.selected.center/latest-1)*100,
        selectedId:result.selectedId,
        regime:result.regime,
        diagnostics:result.diagnostics,
        result
      };
    });
  }

  function modelContributions(regime,horizon){
    let weights=null;
    try{
      weights=SelfLearningAI.effectiveWeights(regime,horizon);
    }catch{}
    if(!weights){
      weights={
        garch:.22,
        "student-t":.22,
        regime:.20,
        ensemble:.24,
        baseline:.12
      };
    }
    const clean={};
    for(const id of Object.keys(MODEL_LABELS)){
      clean[id]=Math.max(weights[id]||0,0);
    }
    const total=Object.values(clean).reduce((a,b)=>a+b,0)||1;
    return Object.fromEntries(
      Object.entries(clean).map(([id,value])=>[id,value/total])
    );
  }

  function confidenceScore(forecasts,contributions){
    const selfState=SelfLearningAI.load();
    const measurementScore=last.measurement?.integratedMetrics?.score||0;
    const selfScore=selfState.confidence||0;
    const dataScore=clamp((last.d?.length||0)/550*100,15,100);
    const modelAgreement=(()=>{
      const returns=forecasts.map(item=>item.returnRate);
      const spread=Math.max(...returns)-Math.min(...returns);
      return clamp(100-spread*4,20,100);
    })();
    const maxContribution=Math.max(...Object.values(contributions));
    const diversification=clamp((1-maxContribution)/.8*100,20,100);

    return clamp(
      dataScore*.28+
      modelAgreement*.28+
      diversification*.14+
      selfScore*.20+
      measurementScore*.10,
      0,
      100
    );
  }

  function decision({forecasts,confidence,riskStyle,capital}){
    const oneWeek=forecasts.find(item=>item.requestedHorizon===5);
    const oneMonth=forecasts.find(item=>item.requestedHorizon===21);
    const threeMonth=forecasts.find(item=>item.requestedHorizon===63);
    const averageReturn=mean(
      [oneWeek,oneMonth,threeMonth]
        .filter(Boolean)
        .map(item=>item.returnRate)
    );
    const worstLow=Math.min(...forecasts.map(item=>item.low));
    const latest=last.d.at(-1).nav;
    const downside=(worstLow/latest-1)*100;
    const adjustment={
      defensive:-1.0,
      standard:0,
      growth:1.0
    }[riskStyle]||0;

    let id,label,className;
    if(confidence>=68&&averageReturn>2-adjustment&&downside>-22){
      id="buy";label="買い";className="v25-buy";
    }else if(confidence>=48&&averageReturn>-1.5-adjustment&&downside>-32){
      id="accumulate";label="積立";className="v25-accumulate";
    }else if(averageReturn>-4-adjustment&&downside>-42){
      id="wait";label="様子見";className="v25-wait";
    }else{
      id="caution";label="注意";className="v25-caution";
    }

    const principalGap=capital.latest.totalValue-capital.latest.principal;
    return {
      id,label,className,
      averageReturn,
      downside,
      principalGap
    };
  }

  function predictionActualRows(){
    const state=SelfLearningAI.load();
    return state.predictions
      .filter(item=>item.evaluated&&Number.isFinite(item.actualNav))
      .slice()
      .reverse()
      .map(item=>({
        date:item.actualDate||item.originDate,
        prediction:item.integratedCenter,
        actual:item.actualNav,
        errorPct:Math.abs(item.integratedCenter-item.actualNav)/item.actualNav*100,
        model:item.selectedModel,
        horizon:item.horizon
      }));
  }

  function run(config){
    if(!last.d?.length){
      throw new Error("先にCSVを読み込み、分析を開始してください。");
    }
    const capital=simulateCostBasis(last.d,config);
    const forecasts=multiHorizonForecast(last.d);
    const reference=forecasts.find(item=>item.requestedHorizon===21)||forecasts[0];
    const contributions=modelContributions(
      reference.regime,
      reference.horizon
    );
    const confidence=confidenceScore(forecasts,contributions);
    const judgement=decision({
      forecasts,
      confidence,
      riskStyle:config.riskStyle,
      capital
    });
    const predictionActual=predictionActualRows();

    return {
      capital,
      forecasts,
      contributions,
      confidence,
      judgement,
      predictionActual,
      createdAt:new Date().toISOString()
    };
  }

  return Object.freeze({
    run,
    labels:()=>({...MODEL_LABELS}),
    simulateCostBasis
  });
})();


const CrashBuyEngine=(()=>{
  const TIERS=[
    {dd:10,extra:20000,label:"小調整"},
    {dd:15,extra:30000,label:"調整"},
    {dd:20,extra:50000,label:"買い増し①"},
    {dd:25,extra:100000,label:"買い増し②"},
    {dd:30,extra:150000,label:"大幅買い"},
    {dd:40,extra:200000,label:"最大級"}
  ];

  function totalReturnValue(row){
    const v=Number(row?.reinvestNav);
    return Number.isFinite(v)&&v>0?v:Number(row?.nav)||0;
  }

  function currentState(rows){
    if(!Array.isArray(rows)||rows.length<2)throw new Error("分析済みCSVデータが必要です。");
    const latest=rows.at(-1);
    const window=rows.slice(-Math.min(252,rows.length));
    const currentTR=totalReturnValue(latest);
    const peakTR=Math.max(...window.map(totalReturnValue).filter(v=>Number.isFinite(v)&&v>0));
    const drawdown=peakTR>0?(currentTR/peakTR-1)*100:0;
    const nav=Number(latest.nav)||0;
    const rawPeak=Math.max(...window.map(r=>Number(r.nav)||0));
    const rawDrawdown=rawPeak>0?(nav/rawPeak-1)*100:0;
    return {latest,nav,currentTR,peakTR,drawdown,rawDrawdown};
  }

  function recommendation(drawdownPct,baseMonthly){
    const depth=Math.max(0,-drawdownPct);
    let tier=null;
    for(const item of TIERS)if(depth>=item.dd)tier=item;
    const extra=tier?tier.extra:0;
    return {
      tier,
      base:Math.max(0,Number(baseMonthly)||0),
      extra,
      total:Math.max(0,Number(baseMonthly)||0)+extra,
      status:tier?tier.label:"通常積立"
    };
  }

  function empiricalReturns(rows){
    const values=rows.map(totalReturnValue).filter(v=>Number.isFinite(v)&&v>0);
    const out=[];
    for(let i=1;i<values.length;i++){
      const r=values[i]/values[i-1]-1;
      if(Number.isFinite(r)&&r>-.95&&r<.95)out.push(r);
    }
    return out;
  }

  function probability(rows,{units,baseMonthly,target,years,runs,extraInvestments=[],actualNav=0}){
    const state=currentState(rows);
    const empirical=empiricalReturns(rows);
    if(empirical.length<30)throw new Error("到達確率の計算に必要な日次データが不足しています。");
    // Ver.27.1: 過去リターンの「形」は使うが、過去の高い平均リターンをそのまま将来へ持ち込まない。
    // 対数リターンを平均0へ中心化し、長期想定ドリフトへ付け替える。
    const empiricalLogs=empirical.map(r=>Math.log1p(r)).filter(Number.isFinite);
    const empiricalLogMean=mean(empiricalLogs);
    const empiricalResiduals=empiricalLogs.map(x=>x-empiricalLogMean);
    units=Math.max(0,Number(units)||0);
    baseMonthly=Math.max(0,Number(baseMonthly)||0);
    target=Math.max(1,Number(target)||3000000);
    years=Math.max(1,Math.floor(Number(years)||1));
    runs=Math.max(200,Math.floor(Number(runs)||3000));

    // Ver.27.5: CSV最終日より後に登録された日付指定の追加投資を将来シミュレーションへ反映。
    const latestDate=rows.at(-1).date;
    const futureExtras=normalizeExtraInvestments(extraInvestments).map(item=>{
      const d=new Date(item.date+"T00:00:00");
      const calendarDays=Math.max(0,(d-latestDate)/86400000);
      const simDay=Math.max(1,Math.round(calendarDays*252/365));
      return {...item,simDay};
    }).filter(item=>new Date(item.date+"T00:00:00")>latestDate&&item.simDay<=years*252);
    const futureExtraMap=new Map();
    for(const item of futureExtras)futureExtraMap.set(item.simDay,(futureExtraMap.get(item.simDay)||0)+item.amount);

    // Ver.27 混合モデル:
    // 45% 過去実績、40% 長期期待リターン、15% 暴落ストレス。
    // 過去の好成績だけを100%再利用して到達確率が過度に楽観化するのを抑える。
    const WEIGHTS={historical:.45,longTerm:.40,stress:.15};
    const LONG_TERM_ANNUAL_RETURN=.07;      // 中立的な長期期待リターン 7%
    const HISTORICAL_DRIFT_CAP=.09;         // 過去成分の将来ドリフトは年率9%で上限固定
    const LONG_TERM_ANNUAL_VOL=.22;         // 年率ボラティリティ 22%
    const dailyMu=Math.log(1+LONG_TERM_ANNUAL_RETURN)/252;
    const historicalDailyMu=Math.log(1+HISTORICAL_DRIFT_CAP)/252;
    const dailySigma=LONG_TERM_ANNUAL_VOL/Math.sqrt(252);

    function normal(rng){
      const u1=Math.max(rng(),1e-12),u2=Math.max(rng(),1e-12);
      return Math.sqrt(-2*Math.log(u1))*Math.cos(2*Math.PI*u2);
    }
    function stressReturn(rng){
      // 通常日は長期モデル。ただし危機局面では連続した負のショックを発生させる。
      // 1日だけの極端値ではなく、数週間〜数か月の下落を表現する。
      return Math.exp(dailyMu+dailySigma*normal(rng))-1;
    }

    const startNav=Math.max(0,Number(actualNav)||0)||state.nav;
    const startValue=units*startNav/10000;
    const startTR=state.currentTR;
    const tradingDays=years*252;
    let success=0;
    const endings=[];
    const hitDays=[];

    for(let k=0;k<runs;k++){
      const rng=makeRng(2700000+k*7919);
      let portfolio=startValue;
      let tr=startTR;
      let peak=Math.max(state.peakTR,tr);
      let fired=new Set();
      let hit=null;
      let stressDays=0;
      let stressDaily=0;

      for(let day=1;day<=tradingDays;day++){
        let r;
        if(stressDays>0){
          r=stressReturn(rng)+stressDaily;
          stressDays--;
        }else{
          const mode=rng();
          if(mode<WEIGHTS.historical){
            // 過去の値動き（歪み・太い裾・ボラ）は残す一方、平均収益は年率9%へ再中心化。
            // これにより直近の非常に強い上昇局面を10年間へ機械的に外挿しない。
            const idx=Math.min(Math.floor(rng()*empiricalResiduals.length),empiricalResiduals.length-1);
            r=Math.exp(historicalDailyMu+(empiricalResiduals[idx]||0))-1;
          }else if(mode<WEIGHTS.historical+WEIGHTS.longTerm){
            r=Math.exp(dailyMu+dailySigma*normal(rng))-1;
          }else{
            // ストレス成分: 年1回前後の判定機会。発動時は累積 -15〜-35% 程度を
            // 20〜60営業日に分散して与える。発動しない日は長期モデルを使用。
            if(rng()<1/252){
              const shock=.15+rng()*.20;
              stressDays=20+Math.floor(rng()*41);
              stressDaily=Math.pow(1-shock,1/Math.max(stressDays,1))-1;
            }
            r=stressReturn(rng)+(stressDays>0?stressDaily:0);
            if(stressDays>0)stressDays--;
          }

          // 単日の異常値でシミュレーションが壊れないよう安全域を設定
          r=clamp(r,-.20,.20);
        }

        tr*=Math.max(1+r,.01);
        portfolio*=Math.max(1+r,.01);
        if(tr>=peak){peak=tr;fired=new Set();}
        const dd=peak>0?(tr/peak-1)*100:0;

        if(day%21===0)portfolio+=baseMonthly;
        const scheduledExtra=futureExtraMap.get(day)||0;
        if(scheduledExtra>0)portfolio+=scheduledExtra;

        const depth=-dd;
        for(const tier of TIERS){
          if(depth>=tier.dd&&!fired.has(tier.dd)){
            portfolio+=tier.extra;
            fired.add(tier.dd);
          }
        }
        if(hit===null&&portfolio>=target)hit=day;
      }
      endings.push(portfolio);
      if(hit!==null){success++;hitDays.push(hit);}
    }
    endings.sort((a,b)=>a-b);
    hitDays.sort((a,b)=>a-b);
    return {
      probability:success/runs*100,
      median:quantile(endings,.5),
      low:quantile(endings,.1),
      high:quantile(endings,.9),
      medianHitDays:hitDays.length?quantile(hitDays,.5):null,
      runs,years,target,startValue,futureExtras,
      model:{weights:WEIGHTS,longTermAnnualReturn:LONG_TERM_ANNUAL_RETURN,historicalDriftCap:HISTORICAL_DRIFT_CAP,longTermAnnualVol:LONG_TERM_ANNUAL_VOL}
    };
  }

  return Object.freeze({TIERS,currentState,recommendation,probability});
})();

function renderCrashBuyAI(){
  const hero=$("crashBuyHero");
  if(!hero)return;
  if(!last.d){
    hero.innerHTML='<div class="small">先にCSVを読み込み、メイン分析を実行してください。</div>';
    return;
  }
  try{
    const units=+$("crashCurrentUnits").value||0;
    const base=+$("crashBaseMonthly").value||0;
    const target=+$("crashTargetValue").value||3000000;
    const years=+$("crashTargetYears").value||1;
    const runs=+$("crashTargetRuns").value||3000;
    const state=CrashBuyEngine.currentState(last.d);
    const actualAnchor=last.v25?.capital?.actualAnchor||null;
    const purchaseNav=actualAnchor?.nav>0?actualAnchor.nav:state.nav;
    const effectiveUnits=actualAnchor?.units>0?actualAnchor.units:units;
    if(actualAnchor&&$("crashCurrentUnits"))$("crashCurrentUnits").value=Math.round(effectiveUnits);
    const rec=CrashBuyEngine.recommendation(state.drawdown,base);
    const addUnits=purchaseNav>0?rec.total/purchaseNav*10000:0;
    const extraUnits=purchaseNav>0?rec.extra/purchaseNav*10000:0;
    const prob=CrashBuyEngine.probability(last.d,{units:effectiveUnits,baseMonthly:base,target,years,runs,extraInvestments:getExtraInvestments(),actualNav:purchaseNav});
    last.crashBuy={state,rec,addUnits,extraUnits,prob};

    const ddClass=(-state.drawdown)>=20?"crash-hot":(-state.drawdown)>=10?"crash-opportunity":"";
    hero.innerHTML=`
      <div class="crash-metric ${ddClass}">
        <div class="label">現在のドローダウン</div>
        <div class="value">${state.drawdown.toFixed(2)}%</div>
        <div class="sub">52週高値比・分配金再投資基準価額ベース<br>通常NAVでは ${state.rawDrawdown.toFixed(2)}%</div>
      </div>
      <div class="crash-metric ${rec.extra>0?"crash-opportunity":""}">
        <div class="label">今月の推奨買付</div>
        <div class="value">${yen(rec.total)}</div>
        <div class="sub">通常 ${yen(rec.base)} ＋ 暴落追加 ${yen(rec.extra)}<br>${rec.status}</div>
      </div>
      <div class="crash-metric">
        <div class="label">予想追加口数</div>
        <div class="value">${(addUnits/10000).toFixed(2)}万口</div>
        <div class="sub">うち暴落追加分 ${(extraUnits/10000).toFixed(2)}万口<br>最新NAV ${Math.round(purchaseNav).toLocaleString()}円</div>
      </div>
      <div class="crash-metric">
        <div class="label">${yen(target)}到達確率</div>
        <div class="value crash-probability">${prob.probability.toFixed(1)}%</div>
        <div class="sub">${years}年以内・${prob.runs.toLocaleString()}回<br>中央値 ${yen(prob.median)}</div>
      </div>`;

    $("crashBuyTable").innerHTML=`<div class="tablewrap"><table><thead><tr><th>ドローダウン</th><th>追加買付</th><th>通常積立込み</th><th>現在の判定</th></tr></thead><tbody>${CrashBuyEngine.TIERS.map(t=>{
      const active=(-state.drawdown)>=t.dd;
      return `<tr${active?' class="active-tier"':''}><td>−${t.dd}%</td><td>${yen(t.extra)}</td><td>${yen(base+t.extra)}</td><td>${active?'到達済み':'未到達'}</td></tr>`;
    }).join("")}</tbody></table></div>`;

    const hitText=prob.medianHitDays?`到達した経路の初回到達中央値は約${(prob.medianHitDays/21).toFixed(1)}か月です。`:`今回の試行では到達経路がありませんでした。`;
    $("crashBuyComment").textContent=`判定基準：52週高値からの税引前分配金再投資基準価額の下落率
現在：${state.drawdown.toFixed(2)}%
今月の参考買付：${yen(rec.total)}
予想追加口数：約${(addUnits/10000).toFixed(2)}万口
${years}年以内に${yen(target)}へ到達する推定確率：${prob.probability.toFixed(1)}%
${hitText}
将来の指定追加投資：${prob.futureExtras.length}件・${yen(prob.futureExtras.reduce((s,x)=>s+x.amount,0))}

Ver.27.5確率モデル：過去実績45%＋長期期待リターン40%（年率7%・ボラ22%）＋暴落ストレス15%を混合。過去実績成分は値動きの形だけを利用し、平均収益率は年率9%を上限として再中心化します。通常積立を毎月、−10/−15/−20/−25/−30/−40%の各段階の追加買付を1暴落局面につき1回だけ実行します。直近の好成績を10年先へそのまま外挿しない参考シミュレーションで、将来の成果を保証しません。`;
  }catch(error){
    console.error("暴落買いAIエラー",error);
    hero.innerHTML=`<div class="status bad">暴落買いAIエラー：${error.message}</div>`;
  }
}

function runV25Dashboard(){
  const status=$("v25Status");
  status.className="status";
  status.textContent="積立元本・分配金・4期間予測を統合しています…";

  setTimeout(()=>{
    try{
      const result=V25DashboardEngine.run({
        initial:+$("initial").value||0,
        monthly:+$("monthly").value||0,
        day:+$("day").value||1,
        taxRate:+$("v25DistributionTax").value||20.315,
        distributionMode:$("v25DistributionMode").value,
        riskStyle:$("v25RiskStyle").value,
        extraInvestments:getExtraInvestments(),
        actualMode:$("v25ActualMode")?.value||"estimated",
        actualUnits:+$("v25ActualUnits")?.value||0,
        actualNav:+$("v25ActualNav")?.value||0,
        actualAvgCost:+$("v25ActualAvgCost")?.value||0,
        actualAcquisitionTotal:+$("v25ActualAcquisitionTotal")?.value||0,
        actualDistributionTotal:+$("v25ActualDistributionTotal")?.value||0,
        actualOrdinaryDistribution:+$("v25ActualOrdinaryDistribution")?.value||0,
        actualSpecialDistribution:+$("v25ActualSpecialDistribution")?.value||0,
        actualTotalReturn:+$("v25ActualTotalReturn")?.value||0
      });

      last.v25=result;
      if(result.capital.actualAnchor){
        if($("crashCurrentUnits"))$("crashCurrentUnits").value=Math.round(result.capital.actualAnchor.units);
        const preview=$("v25ActualAnchorPreview");
        if(preview){
          const a=result.capital.actualAnchor;
          const distGap=a.distributionTotal-(a.ordinaryDistribution+a.specialDistribution);
          preview.textContent=`実績アンカー適用：${Math.round(a.units).toLocaleString()}口 × 基準価額 ${Math.round(a.nav).toLocaleString()}円 → 現在評価額 ${yen(a.marketValue)}。取得原価 ${yen(a.acquisitionTotal)}。分配実績 ${yen(a.distributionTotal)}（普通 ${yen(a.ordinaryDistribution)}＋特別 ${yen(a.specialDistribution)}、内訳差 ${yen(distGap)}）。AI推定分配との差 ${yen(a.distributionTotal-a.estimatedDistributionTotal)}。`;
        }
      }else if($("v25ActualAnchorPreview")){
        $("v25ActualAnchorPreview").textContent="履歴推定モード：初期投資・積立・追加投資・分配再投資から現在値を再構築しています。";
      }
      renderV25Dashboard(result);
      $("exportV25Pdf").disabled=false;
      status.className="status ok";
      renderCrashBuyAI();
      status.textContent="Ver.27.5総合分析が完了しました。";
    }catch(error){
      console.error("Ver.25総合分析エラー",error);
      status.className="status bad";
      status.textContent=`Ver.25総合分析エラー：${error.message}`;
    }
  },60);
}

function renderV25Dashboard(result){
  const labels=V25DashboardEngine.labels();
  const judgement=result.judgement;
  const latest=result.capital.latest;

  $("v25DecisionHero").innerHTML=`
    <div class="v25-confidence-number">${result.confidence.toFixed(0)}点</div>
    <div class="v25-decision ${judgement.className}">${judgement.label}</div>
    <div class="small" style="margin-top:8px">
      4期間平均予想 ${judgement.averageReturn>=0?"+":""}${judgement.averageReturn.toFixed(2)}%
    </div>`;

  $("v25ConfidenceMeter").innerHTML=`
    <div class="v25-meter">
      <span style="width:${result.confidence}%"></span>
    </div>`;

  const decisionText={
    buy:"予測の一致度と信頼度が比較的高い状態です。ただし、一括ではなく分割購入を基本としてください。",
    accumulate:"通常の積立を継続する判断です。価格変動を利用しながら購入単価を平準化します。",
    wait:"方向感が弱い状態です。積立は維持しつつ、大きな追加購入は待つ判断です。",
    caution:"下落側の予測幅が大きいため、追加投資より資金管理を優先する判断です。"
  }[judgement.id];

  $("v25DecisionComment").textContent=`参考判定：${judgement.label}

AI信頼度：${result.confidence.toFixed(0)}点
4期間平均予想：${judgement.averageReturn>=0?"+":""}${judgement.averageReturn.toFixed(2)}%
最も厳しい予測下限：${judgement.downside.toFixed(2)}%
評価額と積立元本の差：${yen(judgement.principalGap)}

${decisionText}

この判定は投資助言ではなく、過去データに基づく参考情報です。`;

  $("v25HorizonCards").innerHTML=result.forecasts.map(item=>`
    <div class="card">
      <div class="card-title">${item.label}</div>
      <div class="card-value">${Math.round(item.center).toLocaleString()}円</div>
      <div class="card-sub">
        ${item.returnRate>=0?"+":""}${item.returnRate.toFixed(2)}%<br>
        ${Math.round(item.low).toLocaleString()}円〜${Math.round(item.high).toLocaleString()}円<br>
        ${labels[item.selectedId]||item.selectedId}
      </div>
    </div>`).join("");

  lineChart(
    $("v25HorizonChart"),
    [
      {
        name:"中心予測",
        color:"#3b82f6",
        values:result.forecasts.map(item=>item.center)
      },
      {
        name:"予測上限",
        color:"#22c55e",
        values:result.forecasts.map(item=>item.high)
      },
      {
        name:"予測下限",
        color:"#ef4444",
        values:result.forecasts.map(item=>item.low)
      }
    ]
  );

  const sortedContributions=Object.entries(result.contributions)
    .sort((a,b)=>b[1]-a[1]);

  $("v25ContributionBars").innerHTML=sortedContributions.map(([id,weight])=>`
    <div class="v25-model-row">
      <span>${labels[id]||id}</span>
      <div class="v25-model-bar">
        <span style="width:${weight*100}%"></span>
      </div>
      <strong>${(weight*100).toFixed(1)}%</strong>
    </div>`).join("");

  const topContribution=sortedContributions[0];
  $("v25ContributionComment").textContent=`現在最も影響の大きいモデルは「${labels[topContribution[0]]||topContribution[0]}」で、貢献度は${(topContribution[1]*100).toFixed(1)}%です。

自己学習データが増えると、局面・予測期間ごとの実績に応じて貢献度が変化します。`;

  $("v25CapitalCards").innerHTML=`
    <div class="card">
      <div class="card-title">積立元本</div>
      <div class="card-value">${yen(latest.principal)}</div>
    </div>
    <div class="card">
      <div class="card-title">${result.capital.actualAnchor?"取得総額（実績）":"推定個別元本"}</div>
      <div class="card-value">${yen(latest.costBasis)}</div>
    </div>
    <div class="card">
      <div class="card-title">現在評価額${result.capital.actualAnchor?"（実績）":""}</div>
      <div class="card-value">${yen(latest.marketValue)}</div>
    </div>
    ${result.capital.actualAnchor?`
    <div class="card">
      <div class="card-title">実保有口数</div>
      <div class="card-value">${Math.round(result.capital.actualAnchor.units).toLocaleString()}口</div>
    </div>
    <div class="card">
      <div class="card-title">平均取得価額（実績）</div>
      <div class="card-value">${(Math.round(result.capital.actualAnchor.averageCostPer10000*100)/100).toLocaleString("ja-JP")}円</div>
    </div>`:""}
    <div class="card">
      <div class="card-title">現金分配金</div>
      <div class="card-value">${yen(latest.cashDistributions)}</div>
    </div>
    ${result.capital.actualAnchor?`
    <div class="card">
      <div class="card-title">累計分配金（実績）</div>
      <div class="card-value">${yen(result.capital.actualAnchor.distributionTotal)}</div>
    </div>
    <div class="card">
      <div class="card-title">普通分配（実績）</div>
      <div class="card-value">${yen(result.capital.actualAnchor.ordinaryDistribution)}</div>
      <div class="card-sub">AI推定 ${yen(result.capital.ordinaryGross)} / 差 ${yen(result.capital.ordinaryGross-result.capital.actualAnchor.ordinaryDistribution)}</div>
    </div>
    <div class="card">
      <div class="card-title">特別分配（実績）</div>
      <div class="card-value">${yen(result.capital.actualAnchor.specialDistribution)}</div>
      <div class="card-sub">AI推定 ${yen(result.capital.specialGross)} / 差 ${yen(result.capital.specialGross-result.capital.actualAnchor.specialDistribution)}</div>
    </div>
    <div class="card">
      <div class="card-title">分配金AI推定誤差</div>
      <div class="card-value">${yen(result.capital.actualAnchor.estimatedDistributionTotal-result.capital.actualAnchor.distributionTotal)}</div>
      <div class="card-sub">実績 ${yen(result.capital.actualAnchor.distributionTotal)} / 推定 ${yen(result.capital.actualAnchor.estimatedDistributionTotal)}</div>
    </div>
    <div class="card">
      <div class="card-title">トータルリターン（実績）</div>
      <div class="card-value">${yen(result.capital.actualAnchor.totalReturn)}</div>
    </div>`:`
    <div class="card">
      <div class="card-title">普通分配推定</div>
      <div class="card-value">${yen(result.capital.ordinaryGross)}</div>
    </div>
    <div class="card">
      <div class="card-title">特別分配推定</div>
      <div class="card-value">${yen(result.capital.specialGross)}</div>
    </div>`}
    <div class="card">
      <div class="card-title">普通分配の推定税額</div>
      <div class="card-value">${yen(result.capital.taxPaid)}</div>
    </div>`;

  const capitalSample=result.capital.history.filter(
    (_,index,array)=>index===array.length-1||index%Math.max(1,Math.floor(array.length/100))===0
  );
  lineChart(
    $("v25CapitalChart"),
    [
      {
        name:"積立元本",
        color:"#f59e0b",
        values:capitalSample.map(item=>item.principal)
      },
      {
        name:"評価額＋現金分配",
        color:"#3b82f6",
        values:capitalSample.map(item=>item.totalValue)
      },
      {
        name:"推定個別元本",
        color:"#22c55e",
        values:capitalSample.map(item=>item.costBasis)
      }
    ]
  );

  const distributionRows=result.capital.distributions.slice(-12).reverse();
  $("v25DistributionTable").innerHTML=distributionRows.length
    ?`<div class="tablewrap"><table>
      <thead>
        <tr>
          <th>日付</th>
          <th>分配金/1万口</th>
          <th>普通分配推定</th>
          <th>特別分配推定</th>
          <th>税額推定</th>
        </tr>
      </thead>
      <tbody>${distributionRows.map(item=>`
        <tr>
          <td>${item.dateText}</td>
          <td>${item.distributionPer10000.toLocaleString()}円</td>
          <td class="v25-tax-normal">${yen(item.ordinary)}</td>
          <td class="v25-tax-special">${yen(item.special)}</td>
          <td>${yen(item.tax)}</td>
        </tr>`).join("")}</tbody>
    </table></div>`
    :'<div class="small">分配実績がありません。</div>';

  $("v25DistributionNote").textContent=`普通分配・特別分配の区分は、各分配日の基準価額と推定平均取得価額を比較した概算です。

実際の税務上の個別元本・普通分配・元本払戻金は、証券会社の取引報告書や税務資料で確認してください。

積立日は入力欄の「積立日」を使い、その日が休業日の場合はCSV上で同月の次の営業日、無ければ月末営業日に購入したものとして計算しています。

${result.capital.actualAnchor?`Ver.27.5実績優先モード：現在評価額・保有口数・取得原価に加え、累計分配金・普通分配・特別分配・トータルリターンも証券会社の入力値を実績アンカーとして表示します。履歴グラフと日別の普通/特別分配内訳は推定ですが、累計実績との差額を確認できます。分配実績は再投資済みの場合があるため、現在評価額へ単純加算してトータルリターンを再計算しません。`:"履歴推定モード：現在値も取引履歴から再構築した推定値です。"}`;

  renderV25ForecastActual(result.predictionActual);

  $("v25Report").textContent=`WCM Analyzer Pro Ver.27.5 総合分析

作成日時：
${new Date(result.createdAt).toLocaleString("ja-JP")}

参考判断：
${judgement.label}

AI信頼度：
${result.confidence.toFixed(0)}点

積立元本：
${yen(latest.principal)}

現在評価額：
${yen(latest.marketValue)}${result.capital.actualAnchor?"（証券会社実績アンカー）":""}

${result.capital.actualAnchor?`実保有口数：
${Math.round(result.capital.actualAnchor.units).toLocaleString()}口

現在基準価額：
${Math.round(result.capital.actualAnchor.nav).toLocaleString()}円

平均取得価額：
${result.capital.actualAnchor.averageCostPer10000.toLocaleString("ja-JP",{maximumFractionDigits:2})}円

取得総額：
${yen(result.capital.actualAnchor.acquisitionTotal)}

累計分配金（実績）：
${yen(result.capital.actualAnchor.distributionTotal)}

普通分配（実績）：
${yen(result.capital.actualAnchor.ordinaryDistribution)}

特別分配（実績）：
${yen(result.capital.actualAnchor.specialDistribution)}

トータルリターン（実績）：
${yen(result.capital.actualAnchor.totalReturn)}

AI推定分配合計との差：
${yen(result.capital.actualAnchor.estimatedDistributionTotal-result.capital.actualAnchor.distributionTotal)}

`:""}評価額と元本の差：
${yen(latest.marketValue-latest.principal)}

普通分配推定累計：
${yen(result.capital.ordinaryGross)}

特別分配推定累計：
${yen(result.capital.specialGross)}

推定税額：
${yen(result.capital.taxPaid)}

4期間平均予想：
${judgement.averageReturn>=0?"+":""}${judgement.averageReturn.toFixed(2)}%

過去予測の実績照合件数：
${result.predictionActual.length}件

本レポートは過去データを用いた参考分析で、将来の運用成果や税務上の取扱いを保証しません。`;
}

function renderV25ForecastActual(rows){
  const chart=$("v25ForecastActualChart");
  const table=$("v25ForecastActualTable");

  if(!rows.length){
    chart.innerHTML='<div class="small">実績照合済みの予測がまだありません。</div>';
    table.innerHTML="";
    return;
  }

  const recent=rows.slice(-30);
  lineChart(
    chart,
    [
      {
        name:"予測値",
        color:"#3b82f6",
        values:recent.map(item=>item.prediction)
      },
      {
        name:"実績値",
        color:"#22c55e",
        values:recent.map(item=>item.actual)
      }
    ]
  );

  table.innerHTML=`<div class="tablewrap"><table>
    <thead>
      <tr>
        <th>実績日</th>
        <th>期間</th>
        <th>予測</th>
        <th>実績</th>
        <th>誤差</th>
      </tr>
    </thead>
    <tbody>${recent.slice().reverse().map(item=>`
      <tr>
        <td>${item.date}</td>
        <td>${item.horizon}営業日</td>
        <td>${Math.round(item.prediction).toLocaleString()}円</td>
        <td>${Math.round(item.actual).toLocaleString()}円</td>
        <td>${item.errorPct.toFixed(2)}%</td>
      </tr>`).join("")}</tbody>
  </table></div>`;
}

function exportV25ReportPdf(){
  if(!last.v25){
    $("v25Status").className="status bad";
    $("v25Status").textContent="先にVer.27.5総合分析を実行してください。";
    return;
  }

  const reportWindow=window.open("","_blank");
  if(!reportWindow){
    $("v25Status").className="status bad";
    $("v25Status").textContent="PDF画面を開けませんでした。Safariのポップアップ設定を確認してください。";
    return;
  }

  const sections=[
    ["AI信頼度と投資判断","v25DecisionHero","v25ConfidenceMeter","v25DecisionComment"],
    ["4期間の予測","v25HorizonCards","v25HorizonChart"],
    ["モデルごとの貢献度","v25ContributionBars","v25ContributionComment"],
    ["積立元本・評価額・分配金","v25CapitalCards","v25CapitalChart","v25DistributionTable","v25DistributionNote"],
    ["過去予測と実績の比較","v25ForecastActualChart","v25ForecastActualTable"],
    ["Ver.25総合レポート","v25Report"]
  ];

  const body=sections.map(([title,...ids])=>`
    <section>
      <h2>${title}</h2>
      ${ids.map(id=>{
        const element=$(id);
        return element?element.outerHTML:"";
      }).join("")}
    </section>`).join("");

  reportWindow.document.open();
  reportWindow.document.write(`<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width">
<title>WCM Analyzer Pro Ver.27.5 分析レポート</title>
<style>
  body{font-family:-apple-system,BlinkMacSystemFont,"Helvetica Neue","Noto Sans JP",sans-serif;margin:24px;color:#172033;background:#fff}
  h1{font-size:26px;margin-bottom:4px}
  h2{font-size:20px;border-bottom:2px solid #2563eb;padding-bottom:7px;margin-top:28px}
  section{break-inside:avoid;margin-bottom:24px}
  .cards{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
  .card,.comment{border:1px solid #cbd5e1;border-radius:10px;padding:12px;margin:6px 0;white-space:pre-wrap}
  .card-title,.small,.card-sub{font-size:12px;color:#64748b}
  .card-value{font-size:20px;font-weight:800}
  .tablewrap{overflow:visible}
  table{width:100%;border-collapse:collapse;font-size:11px}
  th,td{border:1px solid #cbd5e1;padding:6px;text-align:right}
  th:first-child,td:first-child{text-align:left}
  svg{max-width:100%;height:auto}
  .v25-meter,.v25-model-bar{background:#e2e8f0;border-radius:999px;overflow:hidden}
  .v25-meter{height:16px}
  .v25-model-bar{height:10px}
  .v25-meter span,.v25-model-bar span{display:block;height:100%;background:#2563eb}
  .v25-model-row{display:grid;grid-template-columns:140px 1fr 70px;gap:8px;align-items:center;padding:5px 0}
  @media print{
    body{margin:12mm}
    .no-print{display:none}
  }
</style>
</head>
<body>
<h1>WCM Analyzer Pro Ver.27.5 分析レポート</h1>
<p>作成日時：${new Date().toLocaleString("ja-JP")}</p>
${body}
<p style="font-size:10px;color:#64748b;margin-top:30px">
本レポートは過去データに基づく参考分析です。将来の運用成果や税務上の取扱いを保証しません。
</p>
</body>
</html>`);
  reportWindow.document.close();

  setTimeout(()=>{
    reportWindow.focus();
    reportWindow.print();
  },500);
}

document.querySelectorAll(".tab").forEach(button=>{
  button.onclick=()=>{
    document.querySelectorAll(".tab").forEach(item=>item.classList.remove("active"));
    document.querySelectorAll(".page").forEach(page=>page.hidden=true);
    button.classList.add("active");
    $(button.dataset.page).hidden=false;
  };
});
function saveActualAnchorSettings(){
  try{
    localStorage.setItem("wcm-v275-actual-anchor",JSON.stringify({
      mode:$("v25ActualMode")?.value||"actual",
      units:+$("v25ActualUnits")?.value||0,
      nav:+$("v25ActualNav")?.value||0,
      avgCost:+$("v25ActualAvgCost")?.value||0,
      acquisitionTotal:+$("v25ActualAcquisitionTotal")?.value||0,
      distributionTotal:+$("v25ActualDistributionTotal")?.value||0,
      ordinaryDistribution:+$("v25ActualOrdinaryDistribution")?.value||0,
      specialDistribution:+$("v25ActualSpecialDistribution")?.value||0,
      totalReturn:+$("v25ActualTotalReturn")?.value||0
    }));
  }catch(_){}
}
function restoreActualAnchorSettings(){
  try{
    const s=JSON.parse(localStorage.getItem("wcm-v275-actual-anchor")||"null");
    if(!s)return;
    if($("v25ActualMode"))$("v25ActualMode").value=s.mode||"actual";
    if($("v25ActualUnits")&&Number.isFinite(+s.units))$("v25ActualUnits").value=s.units;
    if($("v25ActualNav")&&Number.isFinite(+s.nav))$("v25ActualNav").value=s.nav;
    if($("v25ActualAvgCost")&&Number.isFinite(+s.avgCost))$("v25ActualAvgCost").value=s.avgCost;
    if($("v25ActualAcquisitionTotal")&&Number.isFinite(+s.acquisitionTotal))$("v25ActualAcquisitionTotal").value=s.acquisitionTotal;
    if($("v25ActualDistributionTotal")&&Number.isFinite(+s.distributionTotal))$("v25ActualDistributionTotal").value=s.distributionTotal;
    if($("v25ActualOrdinaryDistribution")&&Number.isFinite(+s.ordinaryDistribution))$("v25ActualOrdinaryDistribution").value=s.ordinaryDistribution;
    if($("v25ActualSpecialDistribution")&&Number.isFinite(+s.specialDistribution))$("v25ActualSpecialDistribution").value=s.specialDistribution;
    if($("v25ActualTotalReturn")&&Number.isFinite(+s.totalReturn))$("v25ActualTotalReturn").value=s.totalReturn;
  }catch(_){}
}
restoreActualAnchorSettings();
["v25ActualMode","v25ActualUnits","v25ActualNav","v25ActualAvgCost","v25ActualAcquisitionTotal","v25ActualDistributionTotal","v25ActualOrdinaryDistribution","v25ActualSpecialDistribution","v25ActualTotalReturn"].forEach(id=>{
  const el=$(id);if(el)el.addEventListener("change",saveActualAnchorSettings);
});

$("distFile").onchange=e=>load(e.target,"dist");$("growthFile").onchange=e=>load(e.target,"growth");$("analyze").onclick=analyze;$("runBacktest").onclick=runForecastValidation;$("runRegime").onclick=runRegimeAnalysis;$("runAdvisor").onclick=runIntegratedAdvisor;$("savePrediction").onclick=saveCurrentPrediction;$("evaluatePredictions").onclick=evaluateSavedPredictions;$("clearLearning").onclick=clearLearningData;$("runAccuracyMeasurement").onclick=runAccuracyMeasurement;$("runStatisticalEngine").onclick=runStatisticalForecast;$("runAdaptiveAI").onclick=runAdaptiveAI;$("resetAdaptiveAI").onclick=resetAdaptiveAI;$("runAutoMode").onclick=runAutoModeDiagnosis;$("loadAutoData").onclick=()=>loadAutomaticCsv();$("analyzeAutoData").onclick=analyzeAutomaticCsv;$("renderFutureChart").onclick=renderFutureNavChart;$("saveLearningPrediction").onclick=saveCurrentLearningPrediction;$("evaluateLearningPredictions").onclick=evaluateSelfLearningPredictions;$("resetSelfLearning").onclick=resetSelfLearningData;$("runMonte").onclick=runMonte;$("compareMonte").onclick=compareMonteMethods;$("runV25Dashboard").onclick=runV25Dashboard;$("recalcCrashBuy").onclick=renderCrashBuyAI;$("exportV25Pdf").onclick=exportV25ReportPdf;$("calcFire").onclick=calcFire;$("calcStress").onclick=renderStress;$("analyzeMarket").onclick=()=>{analyzeMarketEnvironment();if(last.d){renderOutlook();buildMorningBrief()}};$("recalcOutlook").onclick=renderOutlook;$("saveSnapshot").onclick=saveSnapshot;$("clearHistory").onclick=clearHistory;$("whatWouldIDo").onclick=buildWhatWouldIDo;$("saveMemo").onclick=saveDailyMemo;$("clearMemo").onclick=clearDailyMemo;$("download").onclick=download;
$("taxMode").onchange=e=>$("taxRate").disabled=e.target.value==="before";
$("addExtraInvestment").onclick=()=>{createExtraInvestmentRow({});updateExtraInvestStatus();const rows=$("extraInvestmentRows").querySelectorAll(".extra-invest-row");rows[rows.length-1]?.querySelector(".extra-invest-date")?.focus()};
try{const s=JSON.parse(localStorage.getItem("wcm5")||"{}");if(s.start)$("startDate").value=s.start;if(s.initial!=null)$("initial").value=s.initial;if(s.monthly!=null)$("monthly").value=s.monthly;if(s.day)$("day").value=s.day;if(s.taxMode)$("taxMode").value=s.taxMode;if(s.taxRate)$("taxRate").value=s.taxRate;if(Array.isArray(s.extraInvestments)&&!localStorage.getItem("wcm-extra-investments-v272"))localStorage.setItem("wcm-extra-investments-v272",JSON.stringify(s.extraInvestments))}catch(_){}
loadExtraInvestments();
if("serviceWorker"in navigator)navigator.serviceWorker.register("./sw.js?v=275").catch(()=>{});
restoreMarketInputs();

restoreOutlookSettings();
renderHistory();

restoreDailyMemo();

renderLearningSystem();

renderAdaptiveAI();

loadAutomaticCsv({silent:true});

renderSelfLearning();
