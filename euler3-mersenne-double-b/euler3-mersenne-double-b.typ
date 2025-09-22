#set heading(numbering: "1.")


#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox("theorem", "定理", padding: (top: 0em, bottom: 0em))
#let lemma = thmbox("lemma", "補題", padding: (top: 0em, bottom: 0em))
#let definition = thmbox("definition", "定義", padding: (top: 0em, bottom: 0em))
#let corollary = thmbox("corollary", "系", padding: (top: 0em, bottom: 0em))
#let example = thmbox("example", "例", padding: (top: 0em, bottom: 0em))
#let proof = thmproof("proof", "Proof")

#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0"
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#set page(margin: (x: 30pt))

#set text(font: ("New Computer Modern", "Harano Aji Mincho"))

#show heading: it => it + v(10pt)

#let smallspace = [#h(4pt)];
#let even = [even];
#let odd = [odd];
#let prime = [prime];
#let rad = [rad];
#let cophi = $"co"φ$;
#let coφ = cophi;

#let indentbox(body) = context {
  pad(left: 2em, body)
}

#let sub = math.overline

#align(center)[
  #text(size: 18pt)[第三種オイラー超完全数のダブルB型解について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

第三種オイラー超完全数とは, 以下の連立方程式の解のことである:


$ cases(
  sub(h)A=2h phi(a)+sub(h)m+sub(h)",",
  phi(A)=a+m
) $

なお, 慣例で $n-1$ のことを $sub(n)$ と書く.

飯高先生によって始められた一般化された完全数の研究では, 自然数 $alpha, beta$ を固定したとき, $a=alpha p, A=beta q smallspace (p, q: prime, gcd(alpha, p)=gcd(beta, q)=1)$ の形の解が複数個存在するならば, その解をまとめてダブルB型解とよぶ.

#lemma[
  $a, b, c, d$ が無平方数で, $display((φ(a)φ(b))/(a b)=(φ(c)φ(d))/(c d))$ ならば, $a b=c d$.
] <lemma>

これは $phi^k$ 同値の中で証明されている補題 「$I>=1$ 個の無平方数の列 $(alpha_1, ..., alpha_I)$ と $(beta_1, ..., beta_I)$ について, $display(product_(i)phi(alpha_i)/alpha_i=product_(i)phi(beta_i)/beta_i)$ ならば $display(product_i alpha_i=product_i beta_i)$」の $i=2$ の場合である.

#theorem[
  ダブルB型解の係数と平行移動 $alpha, beta$ と $m$ は以下のいずれかを満たす.

  - $display(alpha=1\, beta=2^e h^f\, m=(-h-1-2^e sub(h)h^f)/(h+1))$
  - $alpha=2^e, beta=h^f, m=-sub(h)h^f-h 2^e+sub(h)$
  - $alpha=h^f, beta=2^e, m=-2h^f-2^e+1$
]

#proof[
  今, $(a, A)=(alpha p_0, beta q_0), (alpha p_1, beta q_1)$ がどちらも解であると仮定する.

  $p_0, p_1$ のことをまとめて $p$ と書き, $q_0, q_1$ のことをまとめて $q$ と書くと, 下の連立方程式は2つの解を持つ:

  $ cases(
    sub(h)beta q&=2h phi(alpha)sub(p)+sub(h)m+sub(h)\,,
    phi(beta)sub(q)&=alpha p+m
  ) $

  これは $p, q$ に関する連立一次方程式とみなすことができる.

  よって, その係数行列 $display(mat(sub(h) beta, 2 h phi(alpha); phi(beta), alpha))$ の行列式 $sub(h)alpha beta-2 h phi(alpha)phi(beta)$ は $0$ に等しい.

  したがって $display((phi(alpha)phi(beta))/(alpha beta)=sub(h)/(2 h))$.

  $x=rad(alpha), y=rad(beta)$ とおけば, $display(phi(x)/x=phi(alpha)/alpha\, phi(y)/y=phi(beta)/beta)$ より, $display((phi(x)phi(y))/(x y)=sub(h)/(2h)=(phi(2)phi(h))/(2 h))$.

  したがって @lemma より $rad(alpha)rad(beta)=x y=2h$ で, したがって係数は以下の4パターンがあり得る.

  - $alpha=1, beta=2^e h^f$
  - $alpha=2^e, beta=h^f$
  - $alpha=h^f, beta=2^e$
  - $alpha=2^e h^f, beta=1$

  これらを定義式から 

  $ cases(
    sub(h)beta q&=2h phi(alpha)sub(p)+sub(h)m+sub(h) #h(20pt) &... (upright(A)),
    phi(beta)sub(q)&=alpha p+m &... (upright(B))
  ) $

  に代入する.

  (1) $alpha=1, beta=2^e h^f$ の場合

  #indentbox[
    $ 
      sub(h)2^e h^f q&=2h sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)2^e h^f sub(q)&=2h p+2h m &&... (upright(B)) times 2h
    $

    したがって, $sub(h)2^e h^f=-2h-(h+1)m+sub(h)$ より, $display(m=(-h-1-sub(h)2^e h^f)/(h+1))$ を得る.
  ]

  (2) $alpha=2^e, beta=h^f$ の場合

  #indentbox[
    $
      sub(h)h^f q&=h 2^e sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)h^f sub(q)&=h 2^e p+h m &&... (upright(B)) times 2h
    $

    したがって, $sub(h)h^f=-h 2^e-m+sub(h)$ より, $m=-sub(h)h^f-h 2^e+sub(h)$.
  ]

  (3) $alpha=h^f, beta=2^e$ の場合

  #indentbox[
    $
      sub(h)2^e q&=2sub(h)h^f sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)2^e sub(q)&=2sub(h)h^f p+2sub(h)m &&... (upright(B)) times 2sub(h)
    $

    したがって, $sub(h)2^e=-2sub(h)h^f-sub(h)m+sub(h)$ より, $m=-2 h^f-2^e+1$.
  ]

  (4) $alpha=2^e h^f, beta=1$ の場合

  #indentbox[
    $
      sub(h)q&=sub(h)2^e h^f sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)sub(q)&=sub(h)2^e h^f sub(p)+sub(h)m &&... (upright(B)) times sub(h)
    $

    しかし, これを引くと $sub(h)=-sub(h)2^e h^f+sub(h)$ を得るが, この式は成立しない.
  ]
]
