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
  #text(size: 18pt)[$display(phi(n)/n)$ によって定まる同値類について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

飯高先生は $display(F(n):=sigma(n)/n)$ によって定まる同値類の性質を考察した.

このアイデアをオイラー関数に持ち込んだのが $phi$ 同値である.

主定理の前にいくつか簡単な議論をしておく.

#definition[
  $display(phi(n)/n=phi(m)/m)$ が成り立つとき, $n$ と $m$ は $phi$ 同値であるといい, $n ~_phi m$ と書く.
]

#lemma[
  $rad(n)=rad(m)$ ならば $n~_phi m$.
] <main-thm-converse>

ここで $rad(n)$ は $n$ の根基, つまり $n$ の相異なる素因数の積を表す.

具体的には, $display(rad(n)=product_(p | n)p)$ である.

今回の主定理はこの補題の逆である.

#proof[
  $display(phi(n)=n product_(p | n)(1-1/p))$ より, $display(phi(n)/n=product_(p | n)(1-1/p))$ である.

  さて, $n$ と $m$ の素因数の組が等しければ, $display(phi(n)/n=phi(m)/m)$ が成り立つことは上の式から明らかであろう.
]

#lemma[
  $n$ を無平方数とする.

  自然数 $a, b$ について $a b=n$ が成り立つならば, $gcd(a, b)=1$ で, $a, b$ も無平方数.
] <squarefree-divisors-coprime-squarefree>

無平方数とは, $rad(n)=n$ が成り立つ自然数のことである.

言い換えると, 任意の素数 $p$ について $nu_p (n)<2$ が成り立つ自然数のことである.

#proof[
  $gcd(a, b)=1$ からまず証明する.

  $gcd(a, b)=d>1$ と仮定すると, $d$ には素因数 $p$ が存在する.

  さて, $display(n=a b=a/d dot b/d dot d^2)$ と書け, さらに $display(a/d\, b/d)$ は整数であるから, $n$ は $d^2$ で割れ, よって $n$ は $p^2$ の倍数である.

  これは $n$ が無平方数であることに矛盾.

  次に, $a$ が無平方数でないと仮定すると, $p^2 | a$ を満たす素数 $p$ が存在するが, この $p$ は $p^2 | n$ も満たすことになるので $n$ が無平方数であるという仮定に反する.

  $b$ についても同様.
]

= 主定理

#definition[
  $display(lambda(n):=gcd(phi(n), n)\, lambda'(n):=n/lambda(n))$ と定義する.

  そして, 非負整数 $k$ について, $display(lambda^k (n)=cases(n &"if" k=0\,, lambda(lambda^(k-1) (n)) &"otherwise"))$ と定義する.
]

#proposition[
  $alpha, beta$ を $alpha~_phi beta$ を満たす無平方数とすると, $lambda'(alpha)=lambda'(beta)$ かつ $lambda(alpha)~_phi lambda(beta)$ が成り立つ.
] <lambda-phi-recursion>

#proof[
  $gcd(alpha, phi(alpha))=gcd(lambda(alpha)lambda'(alpha), phi(alpha))=lambda(alpha)$ より, $gcd(lambda'(alpha), phi(alpha))=1$ である.

  よって, $display(phi(alpha)/alpha=phi(alpha)/(lambda(alpha)lambda'(alpha))=((phi(alpha)/lambda(alpha)))/(lambda'(alpha)))$ と変形するとこれは既約分数形である.

  よってユークリッドの補題からある整数 $k$ が存在して $display(beta=k lambda'(alpha)\, phi(beta)=k phi(alpha)/lambda(alpha))$ と書ける.

  このとき, $display(lambda(beta)=gcd(k lambda'(alpha), k phi(alpha)/lambda(alpha))=k gcd(lambda'(alpha), phi(alpha)/lambda(alpha))=k)$ である.

  よって, $beta=lambda(beta)lambda'(alpha)$ から, $lambda'(alpha)=lambda'(beta)$.

  さて, $display(phi(beta)=k phi(alpha)/lambda(alpha)=lambda(beta)phi(alpha)/lambda(alpha))$ に, $alpha=lambda(alpha)lambda'(alpha), beta=lambda(beta)lambda'(beta)$ を代入して @squarefree-divisors-coprime-squarefree を適用すると \ 
  $display(phi(lambda(beta))phi(lambda'(beta))=lambda(beta)(phi(lambda(alpha))phi(lambda'(alpha)))/lambda(alpha))$ を得る.

  両辺を $phi(lambda'(beta))=phi(lambda'(alpha))$ で割って整理すると $display(phi(lambda(beta))/lambda(beta)=phi(lambda(alpha))/lambda(alpha))$, よって $lambda(alpha)~_phi lambda(beta)$ が示された.
]

#theorem[
  $n~_phi m$ ならば $rad(n)=rad(m)$.
]

#proof[
  この定理を証明するには, 

  #align(center)[命題 (A): 無平方数 $alpha, beta$ について $alpha~_phi beta$ ならば $alpha=beta$]

  を示すことができれば十分である.

  というのも, 一般の自然数 $n$ について, @main-thm-converse と $rad$ が冪等であることから $n~_phi rad(n)$.

  
  したがって, $n~_phi m$ というのは $rad(n)~_phi rad(m)$ と同値である.

  任意の自然数 $n$ について $rad(n)$ は無平方数であるから, もし命題 (\*) が示されれば $n~_phi m<==>rad(n)~_phi rad(m)<==>rad(n)=rad(m)$ が示せる.

  そこで, 命題 (A) を証明しよう.

  さて, $lambda(n)$ の定義上 $n>1$ のとき $lambda(n)<n$ であるから, $lambda^i (alpha)=1$ となる正整数 $i$ が存在する.

  今, @lambda-phi-recursion が繰り返し適用できることに注目しよう.

  つまり, $lambda'(alpha)=lambda'(beta)$ かつ $lambda(alpha)~_phi lambda(beta)$ であるが, @squarefree-divisors-coprime-squarefree より $lambda(alpha), lambda(beta)$ も無平方数である.

  したがって, $lambda'(alpha)=lambda'(beta)$ かつ $lambda'(lambda(alpha))=lambda'(lambda(beta))$ かつ $lambda^2 (alpha)~_phi lambda^2 (beta)$.

  このような議論で, $alpha~_phi beta$ に @lambda-phi-recursion を $i$ 回適用すると, すべての $0<=j<i$ について $lambda'(lambda^j (alpha))=lambda'(lambda^j (beta))$ かつ $lambda^i (alpha)~_phi lambda^i (beta)$ が成り立つことがわかる.

  さて, $lambda^i (alpha)=1$ であるから $lambda^i (beta)~_phi 1$.

  よって, $lambda^i (beta)=1$ である.

  ここで, $lambda'(lambda^(i-1)(alpha))=lambda'(lambda^(i-1)(beta))$ なので, $lambda^i (alpha)=lambda^i (beta)$ を $lambda(lambda^(i-1) (alpha))=lambda(lambda^(i-1) (beta))$ と考えれば $lambda^(i-1)(alpha)=lambda^(i-1)(beta)$ が得られる. (これは $lambda(n)lambda'(n)=n$ から.)

  同様に, $lambda'(lambda^(i-2)(alpha))=lambda'(lambda^(i-2)(beta))$ なので, $lambda^(i-1)(alpha)=lambda^(i-1)(beta)$ を $lambda(lambda^(i-2)(alpha))=lambda(lambda^(i-2)(beta))$ と考えれば $lambda^(i-2)(alpha)=lambda^(i-2)(beta)$ も得られる.

  これを繰り返すと, $alpha=beta$ が得られる.
]

最後の命題 (A) の証明を図解すると以下のようになる.

#align(center)[
  #diagram(
    node-outset: 2pt,
    node((0, 0), $alpha~_phi beta$, name: <equiv0>),
    node((0, 1), $lambda(alpha)~_phi lambda(beta)$, name: <equiv1>),
    node((0, 2), $lambda^2 (alpha)~_phi lambda^2 (beta)$, name: <equiv2>),
    node((0, 3), $dots.v$, name: <equiv3>),
    node((0, 4), $lambda^(i-1)(alpha)~_phi lambda^(i-1)(beta)$, name: <equivi-1>),
    node((0, 5), $lambda^i (alpha)~_phi lambda^i (beta)$, name: <equivi>),
    node((1, 0), $lambda'(alpha)=lambda'(beta)$, name: <dasheq0>),
    node((1, 1), $lambda'(lambda(alpha))=lambda'(lambda(beta))$, name: <dasheq1>),
    node((1, 2), $lambda'(lambda^2 (alpha))=lambda'(lambda^2 (beta))$, name: <dasheq2>),
    node((1, 3), $dots.v$),
    node((1, 4), $lambda'(lambda^(i-1)(alpha))=lambda'(lambda^(i-1)(beta))$, name: <dasheqi-1>),
    node((2, 5), $lambda^i (alpha)=lambda^i (beta)$, name: <eqi>),
    node((2, 4), $lambda^(i-1)(alpha)=lambda^(i-1)(beta)$, name: <eqi-1>),
    node((2, 3), $dots.v$, name: <eq3>),
    node((2, 2), $lambda^2 (alpha)=lambda^2 (beta)$, name: <eq2>),
    node((2, 1), $lambda(alpha)=lambda(beta)$, name: <eq1>),
    node((2, 0), $alpha=beta$, name: <eq0>),
    edge(<equiv0>, "=>", <equiv1>),
    edge(<equiv1>, "=>", <equiv2>),
    edge(<equiv2>, "=>", <equiv3>),
    edge(<equiv3>, "=>", <equivi-1>),
    edge(<equivi-1>, "=>", <equivi>),
    edge(<equiv0>, "=>", <dasheq0>),
    edge(<equiv1>, "=>", <dasheq1>),
    edge(<equiv2>, "=>", <dasheq2>),
    edge(<equivi-1>, "=>", <dasheqi-1>),
    edge(<equivi>, "=>", <eqi>),
    edge(<dasheqi-1>, "=>", <eqi-1>),
    edge(<dasheq2>, "=>", <eq2>),
    edge(<dasheq1>, "=>", <eq1>),
    edge(<dasheq0>, "=>", <eq0>),
    edge(<eqi>, "=>", <eqi-1>),
    edge(<eqi-1>, "=>", <eq3>),
    edge(<eq3>, "=>", <eq2>),
    edge(<eq2>, "=>", <eq1>),
    edge(<eq1>, "=>", <eq0>)
  )
]
