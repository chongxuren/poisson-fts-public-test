const repo = 'https://github.com/chongxuren/poisson-fts-public-test';
const track = document.querySelector('#track');
let scores;

function link(text, path) {
  const element = document.createElement('a');
  element.textContent = text;
  element.href = repo + path;
  return element;
}

function table(id, rows, empty, columns) {
  const body = document.getElementById(id);
  body.replaceChildren();
  if (!rows.length) {
    const cell = body.insertRow().insertCell();
    cell.colSpan = columns;
    cell.textContent = empty;
    return;
  }
  for (const data of rows) {
    const row = body.insertRow();
    for (const value of data) row.insertCell().append(value);
  }
}

function render() {
  const selected = track.value;
  const format = n => n === null ? 'Open' : n + ' B';
  document.querySelector('#lower').textContent = format(scores.best['lower-bound']);
  document.querySelector('#upper').textContent = format(scores.best.construction);
  const pr = row => link('#' + row.pr, '/pull/' + row.pr);
  table('ranks', scores.rankings[selected].map((r, i) => [i + 1, r.team, r.bound_bytes, pr(r)]),
        'No qualifying records in this track yet.', 4);
  const history = scores.history.filter(r => r.track === selected).reverse();
  table('history', history.map(r => [pr(r), r.team, r.bound_bytes,
        r.delta === null ? 'Opening record' : r.record ? '+' + r.delta + ' B' : 'No gain',
        link('Verified', '/actions/runs/' + r.run)]), 'No verified submissions in this track yet.', 5);
}

async function load() {
  const status = document.querySelector('#status');
  try {
    // The ledger is committed by the judge. It can change independently of Pages deployments.
    const response = await fetch('https://api.github.com/repos/chongxuren/poisson-fts-public-test/contents/docs/scores.json?ref=main', {
      headers: {Accept: 'application/vnd.github.raw+json'}, cache: 'no-cache'
    });
    if (!response.ok) throw Error(response.status);
    scores = await response.json();
    render();
    status.textContent = 'Scores loaded from the main branch.';
  } catch {
    status.textContent = 'Live scores are unavailable. Open the score ledger below.';
  }
}
track.addEventListener('change', () => { if (scores) render(); });
load();
