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
  #text(size: 18pt)[オイラーIII型メルセンヌ超完全数のダブルB型解について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[2025/08/22]
]

#v(30pt)

= はじめに

宮本 (2023) は第三種オイラー型メルセンヌ完全数を, 以下の連立方程式の解と定めた:

$ cases(
  sub(h) A=2h phi(a)+sub(h)m+sub(h)\,,
  phi(A)=a+m
) $

なお, 慣例で $n-1$ のことを $sub(n)$ と書き, $h$ は奇素数, $m$ は一般の(負になりうる)整数を表す.

この方程式は $a=h dot 2^e, A=h dot 2^e+m+1$ の形の解を持つように設計されている.

しかし, オイラー関数は複雑な関数であるから, 上の形以外の解も存在する.

そこで, そのような例外解が発生する条件や例外解の性質などを調べる研究が発展してきた.

= ダブルB型解

宮本 (2025) は特定の $h$ や $m$ について, ダブルB型解と呼ばれる解の構造が現れることを発見し, その特定の $h, m$ について解を特定した.

ここで, ダブルB型解とは, ある正整数の定数 $alpha, beta$ について, $a=alpha p, A=beta q smallspace (p, q:prime, (alpha, p)=(beta, q)=1)$ と書ける解が2個以上存在することを言う.

下は宮本 (2025) が計算した解の中で典型的なダブルB型解のみを抜き出した表である (したがってこれらがそれぞれの $h, m$ の解をすべて列挙しているわけではない):

#align(center)[
  #stack(
    dir: ltr,
    spacing: 50pt,
    table(
      columns: 2,
      table.header(table.cell(colspan: 2, $h=3, m=-22$)),
      $a$, $A$,
      $2 dot 23$, $3^2 dot 5$,
      $2 dot 29$, $3^2 dot 7$,
      $2 dot 41$, $3^2 dot 11$,
      $2 dot 47$, $3^2 dot 13$,
      $2 dot 59$, $3^2 dot 17$,
      $2 dot 101$, $3^2 dot 31$,
      $2 dot 131$, $3^2 dot 41$,
      $2 dot 137$, $3^2 dot 43$,
      $2 dot 149$, $3^2 dot 47$,
    ),
    table(
      columns: 2,
      table.header(table.cell(colspan: 2, $h=3, m=-19$)),
      $a$, $A$,
      $67$, $2^2 dot 3^2 dot 5$,
      $139$, $2^2 dot 3^2 dot 11$,
      $163$, $2^2 dot 3^2 dot 13$,
      $211$, $2^2 dot 3^2 dot 17$,
      $283$, $2^2 dot 3^2 dot 23$,
      $379$, $2^2 dot 3^2 dot 31$,
      $499$, $2^2 dot 3^2 dot 41$,
      $523$, $2^2 dot 3^2 dot 43$,
      $571$, $2^2 dot 3^2 dot 47$,
    ),
    table(
      columns: 2,
      table.header(table.cell(colspan: 2, $h=3, m=-9$)),
      $a$, $A$,
      $3 dot 7$, $2^2 dot 7$,
      $3 dot 11$, $2^2 dot 13$,
      $3 dot 23$, $2^2 dot 31$,
      $3 dot 31$, $2^2 dot 43$,
      $3 dot 43$, $2^2 dot 61$,
      $3 dot 47$, $2^2 dot 67$,
      $3 dot 67$, $2^2 dot 97$,
      $3 dot 71$, $2^2 dot 103$,
      $3 dot 103$, $2^2 dot 151$,
    )
  )
]

#lemma[
  ダブルB型解の係数 $alpha, beta$ は $display((phi(alpha)phi(beta))/(alpha beta)=sub(h)/(2 h))$ を満たす.
]

#proof[
  今, $(a, A)=(alpha p_0, beta q_0), (alpha p_1, beta q_1)$ がどちらも解であると仮定する. (ただし, $p_0 eq.not p_1, q_0 eq.not q_1$ はすべて素数で, $(alpha, p_0)=(alpha, p_1)=(beta, q_0)=(beta, q_1)=1$ と仮定する.)

  さて, $p_0, p_1$ をまとめて $p$, $q_0, q_1$ をまとめて $q$ と書くと, 下の $p$ と $q$ に関する連立一次方程式は2つ以上の解を持つ:

  $ display(cases(
    sub(h)beta q=2 h phi(alpha)sub(p)+sub(h)m+sub(h),
    phi(beta)sub(q)=alpha p+m
  )) $

  したがって, その係数行列 $display(mat(sub(h)beta, -2h phi(alpha); phi(beta), -alpha))$ の行列式 $-sub(h)alpha beta+2h phi(alpha)phi(beta)$ は $0$ に等しい.

  よって $display((phi(alpha)phi(beta))/(alpha beta)=sub(h)/(2 h))$.
]

さて, これが $alpha, beta$ について何を意味するのか考える.

実は筆者の考案した $phi^k$ 同値の論文の中で証明されている補題を利用すると, ここから即座に $rad(alpha)rad(beta)=2 h$ が言える (ここで $rad(n)$ は $n$ の根基, radicalを表す.)

しかし, 今回はより直感的な理解のため, その補題の限定されたものを利用し, $rad(alpha)rad(beta)=2 h$ を証明してみる.

#lemma[
  正整数 $alpha, beta$ に対して $display((phi(alpha)phi(beta))/(alpha beta)=sub(h)/(2 h))$ ならば, $rad(alpha)rad(beta)=2 h$.
]

#proof[
  $X=rad(alpha)rad(beta)$ とおく.

  このとき, 補助関数 $display(phi'(n):=n product_(p^e || n)(1-1/p)^e)$ とおく.

  すると, $rad(alpha), rad(beta)$ は無平方数であり, さらに $display(phi(alpha)/alpha=product_(p | alpha)(1-1/p))$ であることから ($beta$ についても同様), $display((phi(alpha)phi(beta))/(alpha beta)=(phi'(X))/X)$.

  さて, $display((phi'(X))/X=sub(h)/(2 h)=(sub(h)/2)/h)$ と書くと, 右辺は既約分数形であるから, ある正整数 $k$ を用いて $X=k h$ と書ける.

  $phi'$ が完全乗法的関数, つまり任意の正整数 $n, m$ について $phi'(n m)=phi'(n)phi'(m)$ が成り立つことに注意すると $display((phi'(X))/X=(phi'(k) dot phi'(h))/(h k)=(phi'(k))/k dot sub(h)/h=(sub(h)/2)/h)$.

  よって両辺を比較すると $display((phi'(k))/k=1/2)$.

  右辺は既約分数形であるから, さらにある整数 $k'$ を用いて $k=2k'$ と書ける.

  すると $display((phi'(k))/k=(phi'(k') dot phi'(2))/(2 k')=(phi'(k'))/k' dot 1/2=1/2)$.

  よって $display((phi'(k'))/k'=1)$, だが, $phi'$ の定義より任意の2以上の整数 $n$ について, $n$ は素因数を持っているので $phi'(n)<n$.

  したがって $k'=1$ で, $X=k h=2 h k'=2 h$ と書ける.
]

#theorem[
  第三種オイラー型メルセンヌ超完全数のダブルB型解は, 以下のいずれかに当てはまる:

  - $display(alpha=1\, beta=2^e h^f\, m=(-h-1-2^e sub(h)h^f)/(h+1))$
  - $display(alpha=2^e\, beta=h^f\, m=-sub(h)h^f-h 2^e+sub(h))$
  - $display(alpha=h^f\, beta=2^e\, m=-2h^f-2^e+1)$.
]

#proof[
  先の補題たちより, $rad(alpha)rad(beta)=2 h$ から, $(rad(alpha), rad(beta))$ の組は $(1, 2h), (2, h), (h, 2), (2h, 1)$ のいずれかに分類できる.

  $a=alpha p, A=beta q$ を定義式に代入した式を再掲する:

  $ cases(
    sub(h)beta q&=2h phi(alpha)sub(p)+sub(h)m+sub(h) #h(20pt) &... (upright(A)),
    phi(beta)sub(q)&=alpha p+m &... (upright(B))
  ) $

  (1) $(rad(alpha), rad(beta))=(1, 2h)$ の場合 #indentbox[
    このとき $alpha=1, beta=2^e h^f smallspace (e, f>0)$ と書ける.

    $ 
      sub(h)2^e h^f q&=2h sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)2^e h^f sub(q)&=2h p+2h m &&... (upright(B)) times 2h
    $

    したがって, $sub(h)2^e h^f=-2h-(h+1)m+sub(h)$ より, $display(m=(-h-1-sub(h)2^e h^f)/(h+1))$ を得る.
  ]

  (2) $(rad(alpha), rad(beta))=(2, h)$ の場合 #indentbox[
    このとき $alpha=2^e, beta=h^f smallspace (e, f>0)$ と書ける.

    $
      sub(h)h^f q&=h 2^e sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)h^f sub(q)&=h 2^e p+h m &&... (upright(B)) times 2h
    $

    したがって, $sub(h)h^f=-h 2^e-m+sub(h)$ より, $m=-sub(h)h^f-h 2^e+sub(h)$.
  ]

  (3) $(rad(alpha), rad(beta))=(h, 2)$ の場合 #indentbox[
    このとき $alpha=h^f, beta=2^e smallspace (e, f>0)$ と書ける.

    $
      sub(h)2^e q&=2sub(h)h^f sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)2^e sub(q)&=2sub(h)h^f p+2sub(h)m &&... (upright(B)) times 2sub(h)
    $

    したがって, $sub(h)2^e=-2sub(h)h^f-sub(h)m+sub(h)$ より, $m=-2 h^f-2^e+1$.
  ]

  (4) $rad(alpha), rad(beta))=(2h, 1)$ の場合 #indentbox[
    このとき $alpha=2^e h^f, beta=1 smallspace (e, f>0)$ と書ける.

    $
      sub(h)q&=sub(h)2^e h^f sub(p)+sub(h)m+sub(h) #h(20pt) &&... (upright(A)), \
      sub(h)sub(q)&=sub(h)2^e h^f sub(p)+sub(h)m &&... (upright(B)) times sub(h)
    $

    しかし, これを引くと $sub(h)=-sub(h)2^e h^f+sub(h)$ を得るが, この式は成立しない.
  ]
]


