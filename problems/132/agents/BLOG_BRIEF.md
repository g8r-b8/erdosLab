# Blog post drafting brief (erdos-lab blog, https://g8r-b8.github.io/erdos-lab/)
Source ~/Projects/erdosBlog (README.md; existing _posts/ for tone). `git pull` first. Create drafts ONLY with
`scripts/new-post.sh <problem> "<title>"` (ASCII titles; the script chokes on τ) and fill them in. DO NOT commit/push or
move to _posts/ — publishing needs the user's OK. Author Wingate Jones; no AI mentions (the footer has the single
disclosure line). Front matter: status (new result | partial result | formalised), impact (major | notable | note),
summary, result ($$…$$ math; \lvert X\rvert not |X|), verification (honest map: Lean/axioms, SAT + checker, written
proof, referee passes, numerics — and what was NOT checked), links (code https://github.com/g8r-b8/erdos132-lean,
problem https://www.erdosproblems.com/132). Sections: Background / The result / Idea of the proof / What is still open.
Re-check novelty on the day (forum thread 132, arXiv) and record it. Claims exactly as strong as the sources.
