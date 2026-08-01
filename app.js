"use strict";
const APP_VERSION="9.0";
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
function sampleBootstrap(series,rng){return series[Math.floor(rng()*series.length)]}
function createBlockSampler(series,blockSize,rng){let block=[],position=0;return function(){if(position>=block.length){const maxStart=Math.max(series.length-blockSize,0),start=Math.floor(rng()*(maxStart+1));block=series.slice(start,start+blockSize);if(!block.length)block=[0];position=0}return block[position++]}}
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
    renderWcmDiagnosis(d,rs);
    renderOutlook();

    const best=[...rs].sort((a,b)=>b.value-a.value)[0];
    $("cards").innerHTML=`<div class="card"><div class="card-title">投資元本</div><div class="card-value">${yen(ds.principal)}</div></div><div class="card"><div class="card-title">最も高い方式</div><div class="card-value">${best.name}</div><div class="card-sub">${yen(best.value)}</div></div><div class="card"><div class="card-title">受取分配金</div><div class="card-value">${yen(ds.cash)}</div></div><div class="card"><div class="card-title">推定税額</div><div class="card-value">${yen(ds.tax)}</div></div>`;
    $("compareBody").innerHTML=rs.map(x=>`<tr><td>${x.name}</td><td>${yen(x.principal)}</td><td>${yen(x.value)}</td><td class="${x.profit>=0?"positive":"negative"}">${yen(x.profit)}</td><td>${pct(x.rate)}</td></tr>`).join("");
    $("riskBody").innerHTML=[["CAGR",cagr(d),cagr(g),"%"],["最大下落率",mdd(d),mdd(g),"%"],["年率ボラティリティ",vol(d),vol(g),"%"],["シャープレシオ",sharpe(d),sharpe(g),""],["月間勝率",monthlyWin(d),monthlyWin(g),"%"]].map(x=>`<tr><td>${x[0]}</td><td>${x[1].toFixed(2)}${x[3]}</td><td>${x[2].toFixed(2)}${x[3]}</td></tr>`).join("");
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
function runMonte(){
  if(!last.d)return;
  const years=+$("mcYears").value,runs=+$("mcRuns").value,model=$("mcModel").value,lossBasis=$("lossBasis").value,seed=+$("mcSeed").value||1,blockSize=+$("blockDays").value||21;
  const series=returns(last.d).filter(Number.isFinite);
  if(series.length<30){$("monteResult").innerHTML='<div class="status bad">日次データが不足しています。</div>';return}
  const startValue=last.ds.reinvest,monthly=+$("monthly").value||0,daysPerMonth=21,totalMonths=years*12,totalDays=totalMonths*daysPerMonth,totalContrib=monthly*totalMonths;
  const threshold=lossBasis==="total"?last.ds.principal+totalContrib:startValue;
  const m=mean(series),s=sd(series),results=[],yearly=Array.from({length:years},()=>[]);
  for(let k=0;k<runs;k++){
    const rng=makeRng(seed+k*104729),blockSampler=model==="block"?createBlockSampler(series,blockSize,rng):null;
    let value=startValue;
    for(let d=1;d<=totalDays;d++){
      let r=model==="bootstrap"?sampleBootstrap(series,rng):model==="block"?blockSampler():m+s*normalFromRng(rng);
      value*=Math.max(1+r,.001);
      if(d%daysPerMonth===0)value+=monthly;
      if(d%252===0){const yi=Math.min(Math.floor(d/252)-1,years-1);yearly[yi].push(value)}
    }
    results.push(value)
  }
  results.sort((a,b)=>a-b);
  const p05=quantile(results,.05),p25=quantile(results,.25),median=quantile(results,.5),p75=quantile(results,.75),p95=quantile(results,.95),avg=mean(results);
  const loss=results.filter(v=>v<threshold).length/runs*100,severe=results.filter(v=>v<threshold*.8).length/runs*100;
  const label={bootstrap:"実データ・ブートストラップ",block:"実データ・ブロック法",normal:"比較用・正規分布"}[model];
  $("monteResult").innerHTML=`<div class="cards">
    <div class="card"><div class="card-title">下位5%</div><div class="card-value">${yen(p05)}</div></div>
    <div class="card"><div class="card-title">中央値</div><div class="card-value">${yen(median)}</div></div>
    <div class="card"><div class="card-title">平均値</div><div class="card-value">${yen(avg)}</div></div>
    <div class="card"><div class="card-title">上位5%</div><div class="card-value">${yen(p95)}</div></div>
    <div class="card"><div class="card-title">元本割れ確率</div><div class="card-value">${loss.toFixed(1)}%</div><div class="card-sub">判定額 ${yen(threshold)}</div></div>
    <div class="card"><div class="card-title">20%以上の元本割れ</div><div class="card-value">${severe.toFixed(1)}%</div></div>
  </div><div class="comment" style="margin-top:12px">モデル：${label}
試行回数：${runs.toLocaleString()}回
乱数シード：${seed}
過去の日次リターン件数：${series.length.toLocaleString()}件
25〜75%区間：${yen(p25)}〜${yen(p75)}</div>`;
  const buckets=24,min=results[0],max=results.at(-1),counts=Array(buckets).fill(0);
  results.forEach(v=>counts[Math.min(buckets-1,Math.floor((v-min)/(max-min||1)*buckets))]++);
  lineChart($("monteChart"),[{name:"最終資産の分布",color:"#3b82f6",values:counts}]);
  const rows=yearly.map((v,i)=>{v.sort((a,b)=>a-b);return v.length?`<tr><td>${i+1}年後</td><td>${yen(quantile(v,.05))}</td><td>${yen(quantile(v,.5))}</td><td>${yen(quantile(v,.95))}</td></tr>`:""}).join("");
  $("yearlyMonte").innerHTML=`<div class="tablewrap"><table><thead><tr><th>時点</th><th>下位5%</th><th>中央値</th><th>上位5%</th></tr></thead><tbody>${rows}</tbody></table></div><p class="small">元本割れ確率は、選択した判定基準とCSVの過去データに依存する参考値です。</p>`
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

document.querySelectorAll(".tab").forEach(b=>b.onclick=()=>{
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

document.querySelectorAll(".tab").forEach(x=>x.classList.remove("active"));document.querySelectorAll(".page").forEach(x=>x.hidden=true);b.classList.add("active");$(b.dataset.page).hidden=false});
$("distFile").onchange=e=>load(e.target,"dist");$("growthFile").onchange=e=>load(e.target,"growth");$("analyze").onclick=analyze;$("runMonte").onclick=runMonte;$("calcFire").onclick=calcFire;$("calcStress").onclick=renderStress;$("analyzeMarket").onclick=()=>{analyzeMarketEnvironment();if(last.d)renderOutlook()};$("recalcOutlook").onclick=renderOutlook;$("saveSnapshot").onclick=saveSnapshot;$("clearHistory").onclick=clearHistory;$("download").onclick=download;
$("taxMode").onchange=e=>$("taxRate").disabled=e.target.value==="before";
try{const s=JSON.parse(localStorage.getItem("wcm5")||"{}");if(s.start)$("startDate").value=s.start;if(s.initial!=null)$("initial").value=s.initial;if(s.monthly!=null)$("monthly").value=s.monthly;if(s.day)$("day").value=s.day;if(s.taxMode)$("taxMode").value=s.taxMode;if(s.taxRate)$("taxRate").value=s.taxRate}catch(_){}
if("serviceWorker"in navigator)navigator.serviceWorker.register("./sw.js").catch(()=>{});
restoreMarketInputs();

restoreOutlookSettings();
renderHistory();
