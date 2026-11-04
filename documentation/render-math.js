// Pre-render the TeX in worked-example.src.html to inline SVG, so the published page
// needs no math script at run time.
//   npm install mathjax-full@3.2.2      (anywhere on NODE_PATH)
//   node render-math.js worked-example.src.html worked-example.html
const fs = require('fs');
const {mathjax} = require('mathjax-full/js/mathjax.js');
const {TeX} = require('mathjax-full/js/input/tex.js');
const {SVG} = require('mathjax-full/js/output/svg.js');
const {liteAdaptor} = require('mathjax-full/js/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler} = require('mathjax-full/js/handlers/html.js');
const {AllPackages} = require('mathjax-full/js/input/tex/AllPackages.js');

const [src, out] = process.argv.slice(2);
const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
const doc = mathjax.document('', {
  InputJax: new TeX({packages: AllPackages}),
  OutputJax: new SVG({fontCache: 'local'}),
});

let errors = 0;
const render = (tex, display) => {
  const html = adaptor.outerHTML(doc.convert(tex, {display}));
  if (html.includes('data-mjx-error') || html.includes('merror')) {
    errors++;
    console.error('TeX error in: ' + tex);
  }
  return html;
};

// Math only in prose: <pre> blocks and the inline <svg> tree are left alone.
const parts = fs.readFileSync(src, 'utf8').split(/(<pre[\s\S]*?<\/pre>|<svg[\s\S]*?<\/svg>)/);
const body = parts.map((p, i) => i % 2 ? p : p
  .replace(/\$\$([\s\S]+?)\$\$/g, (_, t) => render(t, true))
  .replace(/\$([^$]+?)\$/g, (_, t) => render(t, false))).join('');

const css = adaptor.textContent(doc.outputJax.styleSheet(doc));
fs.writeFileSync(out, body.replace('</style>', css + '\n</style>'));
if (errors) { console.error(errors + ' TeX errors'); process.exit(1); }
