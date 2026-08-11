const CACHE="wcm-analyzer-v276";
const CORE=["./style.css?v=276","./app.js?v=276","./manifest.json"];

self.addEventListener("install",event=>{
  event.waitUntil(
    caches.open(CACHE).then(cache=>Promise.allSettled(CORE.map(url=>cache.add(url))))
  );
  self.skipWaiting();
});

self.addEventListener("activate",event=>{
  event.waitUntil(
    caches.keys().then(keys=>Promise.all(keys.filter(key=>key!==CACHE).map(key=>caches.delete(key))))
      .then(()=>self.clients.claim())
  );
});

self.addEventListener("fetch",event=>{
  if(event.request.method!=="GET")return;
  const url=new URL(event.request.url);
  const sameOrigin=url.origin===self.location.origin;
  const dynamic=sameOrigin&&(
    event.request.mode==="navigate" ||
    url.pathname.endsWith("/index.html") ||
    url.pathname.endsWith("/wcm_distribution.csv") ||
    url.pathname.endsWith("/wcm_growth.csv") ||
    url.pathname.endsWith("/update-info.json")
  );
  if(dynamic){
    event.respondWith(fetch(event.request,{cache:"no-store"}).catch(()=>caches.match(event.request)));
    return;
  }
  event.respondWith(
    fetch(event.request,{cache:"no-store"}).then(response=>{
      if(response&&response.ok&&sameOrigin){
        const copy=response.clone();
        caches.open(CACHE).then(cache=>cache.put(event.request,copy));
      }
      return response;
    }).catch(()=>caches.match(event.request))
  );
});
