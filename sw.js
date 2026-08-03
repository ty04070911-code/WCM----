const CACHE="wcm-analyzer-v22-2-1-chart-fix";
const ASSETS=[
  "./",
  "./index.html",
  "./style.css",
  "./app.js",
  "./manifest.json",
  "./icon-192.svg",
  "./icon-512.svg"
];

self.addEventListener("install",event=>{
  event.waitUntil(
    caches.open(CACHE).then(cache=>cache.addAll(ASSETS))
  );
  self.skipWaiting();
});

self.addEventListener("activate",event=>{
  event.waitUntil(
    caches.keys().then(keys=>
      Promise.all(
        keys.filter(key=>key!==CACHE).map(key=>caches.delete(key))
      )
    )
  );
  self.clients.claim();
});

self.addEventListener("fetch",event=>{
  if(event.request.method!=="GET")return;

  const url=new URL(event.request.url);
  const isRootData=
    url.origin===self.location.origin&&
    (
      url.pathname.endsWith("/wcm_distribution.csv")||
      url.pathname.endsWith("/wcm_growth.csv")||
      url.pathname.endsWith("/update-info.json")
    );

  if(isRootData){
    event.respondWith(
      fetch(event.request,{cache:"no-store"})
        .then(response=>{
          if(!response||!response.ok)throw new Error("root data fetch failed");
          return response;
        })
        .catch(()=>caches.match(event.request))
    );
    return;
  }

  event.respondWith(
    fetch(event.request,{cache:"no-store"})
      .then(response=>{
        const copy=response.clone();
        caches.open(CACHE).then(cache=>cache.put(event.request,copy));
        return response;
      })
      .catch(()=>caches.match(event.request))
  );
});
