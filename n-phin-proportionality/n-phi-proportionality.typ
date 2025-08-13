#set heading(numbering: "1.")

#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox("theorem", "定理", padding: (top: 0em, bottom: 0em))
#let proposition = thmbox("proposition", "命題", padding: (top: 0em, bottom: 0em))
#let lemma = thmbox("lemma", "補題", padding: (top: 0em, bottom: 0em))
#let definition = thmbox("definition", "定義", padding: (top: 0em, bottom: 0em))
#let corollary = thmbox("corollary", "系", padding: (top: 0em, bottom: 0em))
#let proof = thmproof("proof", "Proof")

#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0"
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#set page(margin: (x: 30pt))

#set text(
  font: ("New Computer Modern", "Harano Aji Mincho"),
  lang: "ja"
)
#show math.equation: set text(
  font: ("New Computer Modern Math", "Harano Aji Mincho")
)
#show heading: it => it + v(10pt)

#let smallspace = [#h(4pt)];
#let even = [even];
#let odd = [odd];
#let prime = [prime];
#let rad = [rad];

#let indentbox(body) = {
  set par(first-line-indent: 2em, hanging-indent: 2em,);
  text[#body]
}

#align(center)[
  #text(size: 18pt)[$n$ と $phi(n)$ の比例関係について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

$n=2phi(n)$ や $n=3phi(n)$ は飯高先生によって調べられており, 解はそれぞれ $n=2^e smallspace (e>0), n=2^e 3^f smallspace (e, f>0)$ の形に書けることが証明されている.

そこで, 今回はより一般な $n$ と $phi(n)$ の比例関係について考察した.

以降, $A, B$ を $gcd(A, B)=1$ を満たす正の定数で, $A n-B phi(n)=0$ の形の方程式の解について考える.

= $A=1$ の場合

#theorem[
  $n-B phi(n)=0$ に解が存在するならば, $B<=3$.
]

#proof[
  $B$ の偶奇で場合分けをする.

  (1) $B:even$ の場合

  $n$ は偶数なので $n=2^e L smallspace (e>0, L:odd)$ と書ける.

  これを $n-B phi(n)=0$ に代入すると $2^e L-B dot 2^(e-1)phi(L)=0$ が得られる.

  両辺を $2^e>0$ で割ると $display(L-B/2 phi(L)=0)$ が得られる.

  さて, $B$ は偶数なので $display(B/2)$ は自然数である.

  ここで $L eq.not 1$ とすると, $phi(L)$ は偶数であるが, これは $L$ が奇数であることに矛盾.

  よって $L=1$ であるが, このとき $display(1-B/2=0)$, つまり $B=2$ であり, $B<=3$.

  (2) $B:odd$ の場合

  いま $B>4$ を仮定しているので, $B$ は素因数をもつ.

  したがって, $B=p D smallspace (p:odd prime, D:odd)$ と書ける.

  さて, $n-B phi(n)=0$ より $n$ も $p$ の倍数であるから, $n=p^e L smallspace (e>0, p cancel(divides) L)$ と書ける.

  これと $B=p D$ を $n-B phi(n)=0$ に代入すると $p^e L-p^e D (p-1)phi(L)=0$ を得る.

  両辺を $p^e>0$ で割ると $L-D(p-1)phi(L)=0$ となる.

  さて, $p-1$ は偶数であるから, $D(p-1)$ も偶数.

  したがって, $D(p-1)>=4$ のときは先ほど示したように解は存在しない.

  よって, 解が存在するとすれば $D(p-1)<=3$ の場合であるが, これを満たす唯一の $D, p$ は $D=1, p=3$ である.

  すると $B=p D=3$ であるが, これは $B<=3$ を満たす.
]

3. $A:odd$ の場合

#theorem[
  $A:odd>1, gcd(A, B)=1$ とする.

  $A n-B phi(n)=0$ に解が存在するならば, $2 || p-1$ を満たす奇素数 $p$ を用いて $display(A=(p-1)/2\, B=p)$ と書け, \
  さらにこのときの解は $n=2^e p^f smallspace (e, f>0)$ と書ける.
]

#proof[
  $gcd(A, B)=1, A>1$ より $A eq.not 1$, したがって $n eq.not 1$.

  また, $n$ は2のべきではない; $n$ が2のべきであるとすると, $A n-B phi(n)=0$ を満たしながら $gcd(A, B)=1$ を満たす組は $(A, B)=(1, 2)$ しかなく, $A>1$ の仮定に反するからである.

  よって $n>=3$ より $phi(n)$ が偶数, したがって $n$ も偶数で, $n=2^e L smallspace (e>0, L:odd)$ と書ける.

  これを $A n-B phi(n)=0$ に代入すると $A dot 2^e L-B 2^(e-1)phi(L)=0$.

  両辺を $2^(e-1)>0$ で割って $2A L-B phi(L)=0$ を得る.

  (1) $B$ が偶数の場合

  $2A L-B phi(L)=0$ は $display(L=B/2 dot phi(L)/A)$ と書き直せる.

  ここで $B$ は偶数なので $display(B/2)$ は自然数だが, $gcd(A, B)=1$ より $display(phi(L)/A)$ は自然数.

  しかし $n$ は2のべきではないので, $L>1$ より $phi(L)$ は偶数.

  すると $display(phi(L)/A)$ も偶数となるが, これは $L$ が奇数であることに矛盾.

  (2) $B$ が奇数の場合

  $B, A, L$ はすべて奇数なので, $2A L-B phi(L)=0$ より $nu_2 (phi(L))=1$.

  さて, $display(phi(L)=product_(p^e || L)p^(e-1)(p-1))$ より, $L$ は素因子を1つしか持てない.

  よって $L=p^f smallspace (f>0, p:odd prime)$ と書け, また $nu_2 (p-1)=1$ より $2 || p-1$.

  これを $2 A L-B phi(L)=0$ に代入すると $2A dot p^f-B dot p^(f-1)(p-1)=0$ を得る.

  両辺を $p^(f-1)>0$ で割ると $2 A p-B (p-1)=0$ となり, したがって $display(A p=B (p-1)/2)$.

  さて, $display(gcd(p, (p-1)/2)=1)$ より $B$ は $p$ の倍数である.

  そこで $display(D=B/p)$ とおくと $A=D (p-1)/2$.

  しかし $gcd(A, B)=1$ から $gcd(A, D)=1$ より, $D=1$.

  したがって $display(B=p\, A=(p-1)/2)$

  このとき $n=2^e L=2^e p^f$.
]
