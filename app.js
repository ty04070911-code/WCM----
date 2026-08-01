"use strict";
const APP_VERSION="13.0";

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
function sd(a){if(a.length<2)return 0;const m=mean(a);return Math.sqrt(a.reduce((s,v)=>s+(v-m)**2,0)/(a.length-1))}
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
function plan(rows,initial,monthly,day){
  const map=new Map();if(initial>0)map.set(rows[0].dateText,initial);
  const g=new Map();rows.forEach(r=>{const k=`${r.date.getFullYear()}-${r.date.getMonth()+1}`;(g.get(k)||g.set(k,[]).get(k)).push(r)});
  [...g.values()].slice(1).forEach(rs=>{if(monthly<=0)return;const r=rs.find(x=>x.date.getDate()>=day)||rs.at(-1);map.set(r.dateText,(map.get(r.dateText)||0)+monthly)});
  return map
}
function simDist(rows,initial,monthly,day,taxRate){
  const p=plan(rows,initial,monthly,day),tm=1-taxRate/100;let ru=0,iu=0,principal=0,cash=0,tax=0;const h=[];
  for(const r of rows){
    const a=p.get(r.dateText)||0;if(a>0){const u=a/r.nav*10000;ru+=u;iu+=u;principal+=a}
    if(r.distribution>0){
      const gross=ru*r.distribution/10000,net=gross*tm;cash+=net;tax+=gross-net;
      const ri=iu*r.distribution/10000*tm;iu+=ri/r.nav*10000
    }
    const market=ru*r.nav/10000,total=market+cash,reinvest=iu*r.nav/10000;
    h.push({date:r.date,dateText:r.dateText,principal,market,cash,total,reinvest,tax})
  }
  return {principal,market:h.at(-1).market,cash,total:h.at(-1).total,reinvest:h.at(-1).reinvest,tax,history:h}
}
function simGrowth(rows,initial,monthly,day){
  const p=plan(rows,initial,monthly,day);let units=0,principal=0;const h=[];
  for(const r of rows){const a=p.get(r.dateText)||0;if(a>0){units+=a/r.nav*10000;principal+=a}h.push({date:r.date,dateText:r.dateText,principal,value:units*r.nav/10000})}
  return {principal,value:h.at(-1).value,history:h}
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
      for(let d=0;d<21;d++)value*=Math.max(1+sampleBootstrap(series,rng),.001);
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

function analyze(){
  try{
    const s=new Date($("startDate").value+"T00:00:00"),start=Math.max(s,distData[0].date,growthData[0].date),end=Math.min(distData.at(-1).date,growthData.at(-1).date);
    if(start>=end)throw new Error("共通期間がありません");
    const d=distData.filter(r=>r.date>=start&&r.date<=end),g=growthData.filter(r=>r.date>=start&&r.date<=end);
    const initial=+$("initial").value||0,monthly=+$("monthly").value||0,day=+$("day").value||1,tax=$("taxMode").value==="after"?(+$("taxRate").value||0):0;
    if(initial<=0&&monthly<=0)throw new Error("投資額を入力してください");
    const ds=simDist(d,initial,monthly,day,tax),gs=simGrowth(g,initial,monthly,day);
    const rs=[result("分配金受取",ds.principal,ds.total),result("分配金再投資",ds.principal,ds.reinvest),result("資産成長型",gs.principal,gs.value)];
    last={d,g,ds,gs,rs};
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
    $("resultArea").hidden=false;$("mainStatus").className="status ok";$("mainStatus").textContent="分析完了";localStorage.setItem("wcm5",JSON.stringify({start:$("startDate").value,initial,monthly,day,taxMode:$("taxMode").value,taxRate:$("taxRate").value}));
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
  const need=+$("monthlyNeed").value||0;
  const wr=(+$("withdrawRate").value||4)/100;
  const dy=(+$("distributionYield").value||10)/100;
  const annual=need*12;
  const fire=annual/wr;
  const dist=annual/dy;
  const current=last.ds?.reinvest||0;
  const sim=fireMonteCarlo();

  $("fireResult").innerHTML=`
    <div class="cards">
      <div class="card"><div class="card-title">取崩型必要資産</div><div class="card-value">${yen(fire)}</div><div class="card-sub">現在との差 ${yen(Math.max(fire-current,0))}</div></div>
      <div class="card"><div class="card-title">分配金生活必要資産</div><div class="card-value">${yen(dist)}</div><div class="card-sub">現在との差 ${yen(Math.max(dist-current,0))}</div></div>
      <div class="card"><div class="card-title">目標年齢での達成確率</div><div class="card-value">${sim?sim.probability.toFixed(1):"0.0"}%</div><div class="card-sub">${sim?sim.years:0}年後</div></div>
      <div class="card"><div class="card-title">目標時点の中央値</div><div class="card-value">${sim?yen(sim.median):yen(0)}</div></div>
    </div>
    ${sim?`<div class="comment" style="margin-top:12px">目標資産：${yen(sim.target)}
下位5%：${yen(sim.low)}
中央値：${yen(sim.median)}
上位5%：${yen(sim.high)}

達成確率は過去の日次リターンを再抽出した1,000回の参考シミュレーションです。</div>`:""}`
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

document.querySelectorAll(".tab").forEach(button=>{
  button.onclick=()=>{
    document.querySelectorAll(".tab").forEach(item=>item.classList.remove("active"));
    document.querySelectorAll(".page").forEach(page=>page.hidden=true);
    button.classList.add("active");
    $(button.dataset.page).hidden=false;
  };
});
$("distFile").onchange=e=>load(e.target,"dist");$("growthFile").onchange=e=>load(e.target,"growth");$("analyze").onclick=analyze;$("runBacktest").onclick=runForecastValidation;$("runMonte").onclick=runMonte;$("compareMonte").onclick=compareMonteMethods;$("calcFire").onclick=calcFire;$("calcStress").onclick=renderStress;$("analyzeMarket").onclick=()=>{analyzeMarketEnvironment();if(last.d){renderOutlook();buildMorningBrief()}};$("recalcOutlook").onclick=renderOutlook;$("saveSnapshot").onclick=saveSnapshot;$("clearHistory").onclick=clearHistory;$("whatWouldIDo").onclick=buildWhatWouldIDo;$("saveMemo").onclick=saveDailyMemo;$("clearMemo").onclick=clearDailyMemo;$("download").onclick=download;
$("taxMode").onchange=e=>$("taxRate").disabled=e.target.value==="before";
try{const s=JSON.parse(localStorage.getItem("wcm5")||"{}");if(s.start)$("startDate").value=s.start;if(s.initial!=null)$("initial").value=s.initial;if(s.monthly!=null)$("monthly").value=s.monthly;if(s.day)$("day").value=s.day;if(s.taxMode)$("taxMode").value=s.taxMode;if(s.taxRate)$("taxRate").value=s.taxRate}catch(_){}
if("serviceWorker"in navigator)navigator.serviceWorker.register("./sw.js").catch(()=>{});
restoreMarketInputs();

restoreOutlookSettings();
renderHistory();

restoreDailyMemo();
