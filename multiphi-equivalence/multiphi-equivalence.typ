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
  #text(size: 18pt)[$phi^k$ 同値について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

以前, $n~_phi m <==> display(phi(n)/n=phi(m)/m)$ によって定義される $phi$ 同値の条件を解明した.

具体的には, $n~_phi m <==> rad(n)=rad(m)$ がわかった.

ただし, $rad$ は根基を指す; つまり, $display(rad(n)=product_(p | n)p)$.

今回はその一般化について考察する.

なお, $phi^k (n)$ は $phi$ の $k$ 回合成とし, 特に $phi^0 (n)=n$ と考える.

以下は, 整数論でよく使われる記号である.

#definition[
  正整数 $n$ と素数 $p$ に対し, $p^e divides n$ を満たす非負整数 $e$ のうち最大のものを $nu_p (n)$ と書き, $n$ の $p$ 進付値と呼ぶ.
]

$p$ を固定すれば, $nu_p (n)$ は完全加法的関数である; つまり, 任意の (互いに素とは限らない) 正整数 $a, b$ について, $nu_p (a b)=nu_p (a)+nu_p (b)$.

= 弱い条件

結論から述べると, $display((phi^k (n))/n=(phi^k (m))/m ==> rad(n)=rad(m))$ が言える.

さて, その証明のために補助関数とその性質を用意する.

= 重複オイラー関数とその性質

#definition[
  正整数 $n$ に対し, 関数 $phi'$ を $display(phi'(n)=n product_(p^e || n)(1-1/p)^e)$ で定義し, 重複オイラー関数と呼ぶ.

  そして, $display((phi'(n))/n=(phi'(m))/m)$ が成り立つことを $n~_(phi')m$ と書く.
]

なお, 記号 $p^e || n$ は $n$ が $p^e$ をちょうど割り切る, つまり $e$ は $p^e | n$ を満たす最大の非負整数であることを表す.

例えば, $n=2^3 dot 5^6 dot 11^7$ のとき, $display(phi'(n)=n dot (1-1/2)^3 dot (1-1/5)^6 dot (1-1/11)^7)$ となる.

さて, $display(phi'(n)=product_(p^e || n)(p-1)^e)$ とも書ける

したがって, 任意の正整数 $a, b$ に対して, $display(phi'(a b)=product_(p | a b)(p-1)^(nu_p (a b))=product_(p | a b)(p-1)^(nu_p (a)+nu_p (b)))$ より, $phi'(a b)=phi'(a)phi'(b)$ が成り立つ.

オイラー関数とは異なり, これは $a, b$ が互いに素とは限らなくとも成り立つ.

このことを, $phi'$ は完全乗法的であるという.

#proposition[
  $I$ を正整数とする. 無平方数の正整数からなる数の組 $(alpha_1, alpha_2, ... ,alpha_I)$ について, \
  $display(A=product_(i=1)^I alpha_i)$ とおくと, $display(product_(i=1)^I phi(alpha_i)/alpha_i=(phi'(A))/A)$ が成り立つ.
] <multiplephi>

#proof[
  任意の無平方数 $alpha$ について, $phi'$ の定義より $phi'(alpha)=phi(alpha)$ である.

  というのも, $alpha$ の素因数分解の指数は必ず1であるからである.

  すると証明すべき式は $display(product_(i=1)^I (phi'(alpha_i))/(alpha_i)=(phi'(A))/A)$ となるが, これは重複オイラー関数の完全乗法性から成り立つことがわかる.
]

#definition[
  $display(lambda (n)=gcd(phi'(n), n)\, lambda'(n)=n/(lambda (n)))$ と定義する.

  そして, 非負整数 $k$ について, $display(lambda^k (n)=cases(n & "if" k = 0, lambda(lambda^(k-1) (n)) & "otherwise"))$ と定義する.
]

#lemma[
  $n~_(phi')m$ が成り立つならば, $lambda'(n)=lambda'(m)$ かつ $lambda(n)~_(phi')lambda(m)$.
] <dupphi_reduction>

#proof[
  $display(gcd(lambda'(n), (phi'(n))/lambda(n))=gcd(n/lambda(n), (phi'(n))/lambda(n))=1)$.

  したがって, $display((phi'(n))/n=((phi'(n))/lambda(n))/(n/lambda(n))=((phi'(n))/lambda(n))/(lambda'(n)))$ は既約分数形で, これは $display((phi'(m))/m)$ に等しい.

  よって, 既約分数の一意性から, ある整数 $k$ が存在して $display(m=k lambda'(n)\, phi'(m)=k (phi'(n))/(lambda(n)))$ と書ける.

  ここで, $display(lambda(m)=gcd(m, phi'(m))=gcd(k lambda'(n), k (phi'(n))/lambda(n))=k gcd(lambda'(n), (phi'(n))/lambda(n))=k)$.

  $m=k lambda'(n)$ と $m=lambda(m)lambda'(m)=k lambda'(m)$ を比較すれば, $lambda'(n)=lambda'(m)$ を得る.

  さて, $phi'$ は完全乗法的関数であるから, $display((phi'(m))/m=(phi'(lambda(m)lambda'(m)))/(lambda(m)lambda'(m))=(phi'(lambda(m)))/(lambda(m)) dot (phi'(lambda'(m)))/(lambda'(m)))$.

  一方, $display((phi'(n))/n=(phi'(lambda(n)lambda'(n)))/(lambda(n)lambda'(n))=(phi'(lambda(n)))/lambda(n) dot (phi'(lambda'(n)))/(lambda'(n)))$.

  $n~_(phi')m$ と $lambda'(n)=lambda'(m)$ を利用すれば, $display((phi'(lambda(n)))/lambda(n)=(phi'(lambda(m)))/lambda(m))$, つまり $lambda(n)~_(phi')lambda(m)$ が得られる.
]

#proposition[
  任意の正整数 $n, m$ に対し, $display(n~_(phi')m <==> n=m)$.
] <dupphi-injection>

#proof[
  $phi'(n)$ は定義より, $n>1$ のとき $phi'(n)<n$ を満たす.

  よって, $n>1$ のとき $lambda(n)<n$ であるから, $lambda^i (n)=1$ を満たす正整数 $i$ が存在する.

  さて, ここで先の補題が繰り返し適用できることに着目する.

  つまり, まず $n~_(phi')m$ を @dupphi_reduction に適用すると, $lambda(n)~_(phi')lambda(m)$ が得られ, これをさらに @dupphi_reduction に適用すると $lambda^2 (n)~_(phi')lambda^2 (m)$ が得られる.

  これを繰り返すことで, 任意の非負整数 $j$ について $lambda^j (n)~_(phi')lambda^j (m) quad ..."(I)"$ が言える.

  さて, $lambda^j (n)~_(phi')lambda^j (m)$ に @dupphi_reduction を適用すれば, 任意の非負整数 $j$ について $lambda'(lambda^j (n))=lambda'(lambda^j (m)) quad ..."(II)"$ が言える.

  ここで $j=i$ の場合について考える.

  式(I) に $j=i$ を代入して $lambda^i (n)~_(phi')lambda^i (m)$ を得るが, $lambda^i (n)=1$ から $display((phi'(lambda^i (m)))/(lambda^i (m))=(phi'(1))/1=1)$.

  しかし, $phi'(n)$ の定義より一般の $n$ について $n>1$ ならば $phi'(n)<n$ であるから, $lambda^i (m)=1$ が得られる.

  よって, $lambda^i (n)=lambda^i (m)$.

  さて, $lambda^(i-1) (n)=lambda(lambda^(i-1) (n))lambda'(lambda^(i-1) (n))=lambda^i (n)lambda'(lambda^(i-1) (n))$ で, いま式(II) より $lambda'(lambda^(i-1)(n))=lambda'(lambda^(i-1)(m))$ も成り立つので, $lambda^(i-1)(n)=lambda^(i-1)(m)$.

  さらに, $lambda^(i-2)(n)=lambda(lambda^(i-2)(n))lambda'(lambda^(i-2)(n))=lambda^(i-1)(n)lambda'(lambda^(i-2)(n))$ で, いま式(II) より $lambda'(lambda^(i-2)(n))=lambda'(lambda^(i-2)(m))$ も成り立つので, $lambda^(i-2)(n)=lambda^(i-2)(m)$.

  これを繰り返すことにより, $n=m$ を得ることができる.

  #align(center)[
    #diagram(
      node-outset: 2pt,
      node((0, -0.5), "式(I)"),
      node((0, 0), $n~_phi' m$, name: <equiv0>),
      node((0, 1), $lambda(n)~_phi' lambda(m)$, name: <equiv1>),
      node((0, 2), $lambda^2 (n)~_phi' lambda^2 (m)$, name: <equiv2>),
      node((0, 3), $dots.v$, name: <equiv3>),
      node((0, 4), $lambda^(i-1)(n)~_phi' lambda^(i-1)(m)$, name: <equivi-1>),
      node((0, 5), $lambda^i (n)~_phi' lambda^i (m)$, name: <equivi>),
      node((1, -0.5), "式(II)"),
      node((1, 0), $lambda'(n)=lambda'(m)$, name: <dasheq0>),
      node((1, 1), $lambda'(lambda(n))=lambda'(lambda(m))$, name: <dasheq1>),
      node((1, 2), $lambda'(lambda^2 (n))=lambda'(lambda^2 (m))$, name: <dasheq2>),
      node((1, 3), $dots.v$),
      node((1, 4), $lambda'(lambda^(i-1)(n))=lambda'(lambda^(i-1)(m))$, name: <dasheqi-1>),
      node((2, 5), $lambda^i (n)=lambda^i (m)$, name: <eqi>),
      node((2, 4), $lambda^(i-1)(n)=lambda^(i-1)(m)$, name: <eqi-1>),
      node((2, 3), $dots.v$, name: <eq3>),
      node((2, 2), $lambda^2 (n)=lambda^2 (m)$, name: <eq2>),
      node((2, 1), $lambda(n)=lambda(m)$, name: <eq1>),
      node((2, 0), $n=m$, name: <eq0>),
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
]

さて, 上のふたつから, 次の補題を導くことができる.

#lemma[
  $n, m, k$ を正整数とする. $display((phi^k (n))/n=(phi^k (m))/m)$ と \
  $display(rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m)))$ は同値である.
] <multiphi-equivalent-condition>

#proof[
  $display((phi^k (n))/n)$ を $display(phi(n)/n dot (phi^2 (n))/phi(n) dot (phi^3 (n))/(phi^2 (n)) dot ... dot (phi^k (n))/(phi^(k-1) (n)))$ と変形する.

  さらに, 一般に正整数 $x$ について $display(phi(x)/x=phi(rad(x))/rad(x))$ より, $display((phi^k (n))/n=(phi^k (m))/m)$ は \

  $display(phi(rad(n))/rad(n) dot phi(rad(phi(n)))/rad(phi(n)) dot ... dot phi(rad(phi^(k-1) (n)))/rad(phi^(k-1) (n))=phi(rad(m))/rad(m) dot phi(rad(phi(m)))/rad(phi(m)) dot ... dot phi(rad(phi^(k-1) (m)))/rad(phi^(k-1) (m)))$

  と同値である.

  $N=rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n)), M=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m))$ とおくと, \
  正整数の根基は無平方数であることと @multiplephi から 上の式は $display((phi'(N))/N=(phi'(M))/M)$ に同値で, \
  これは @dupphi-injection から $N=M$ に同値である.
]

さて, $N=M$ は $n~_(phi^k) m$ よりは扱いやすいが, 証明にはまだ補題が必要である.

#lemma[
  $p$ を素数, $n$ を正整数とする.

  $display(nu_p (phi(n))=max(0, nu_p (n)-1)+sum_(q>p, q | n)nu_p (q-1).)$
] <nu_p_phi>

#proof[
  $display(nu_p (phi(n))=nu_p (product_(q^e || n) q^(e-1)(q-1)))$.

  (1) $p | n$ の場合 #indentbox[
    $display(nu_p (phi(n))=nu_p (p^(nu_p (n)-1)(p-1) dot product_(q^e || n, q eq.not p) q^(e-1)(q-1))=nu_p (n)-1+nu_p (product_(q^e || n, q eq.not p) q^(e-1)(q-1)))$.

    $p | n$ から $nu_p (n)>=1$ なので, $nu_p (n)-1=max(0, nu_p (n)-1)$.

    したがって $display(nu_p (product_(q^e || n,q eq.not p)q^(e-1)(q-1))=sum_(q>p,q | n)nu_p (q-1))$ が言えれば十分.
  ]

  (2) $p divides.not n$ の場合 #indentbox[
    $display(nu_p (phi(n))=nu_p (product_(q^e || n) q^(e-1)(q-1))=nu_p (product_(q^e || n, q eq.not p) q^(e-1)(q-1)))$.

    $p divides.not n$ から $nu_p (n)=0$ なので, $max(0, nu_p (n)-1)=0$.

    したがってこの場合も $display(nu_p (product_(q^e || n,q eq.not p)q^(e-1)(q-1))=sum_(q>p,q | n)nu_p (q-1))$ が言えれば十分.
  ]

  よって $display(nu_p (product_(q^e || n, q eq.not p) q^(e-1)(q-1))=sum_(q>p, q | n)nu_p (q-1))$ を示す.

  まず, $q$ が $p$ ではない素数なので, $q^e$ は $p$ の倍数にはならない.

  したがって, $display(nu_p (product_(q^e || n, q eq.not p) q^(e-1)(q-1))=nu_p (product_(q^e || n, q eq.not p) (q-1)))$ で, $nu_p$ の完全加法性からこれは $display(sum_(q^e || n, q eq.not p) nu_p (q-1))$ に等しい.

  さて, $e$ はもう使わないので条件 $q^e || n$ は $q | n$ と書き換えてよく, 上の式は $display(sum_(q | n, q eq.not p) nu_p (q-1))$ となる.

  ここで, $q<p$ であれば, $nu_p (q-1)$ は $0$ であるから, この総和は $q>p$ の場合だけとってもよい.

  つまり, これは $display(sum_(q | n, q > p)nu_p (q-1))$ に等しい.
]

主定理の証明の前に, もう一つ補題を証明しておく. (この補題の位置づけは, 主定理の証明の流れを見てからのほうがわかりやすいであろう.)

#lemma[
  $n, m, i$ を正整数, $p$ を素数とする.

  $p | n, p divides.not m, p divides.not phi^i (n), p | phi^i (m)$ が成り立つならば, ある素数 $q>p$ と $0<=j<i$ を満たす整数 $j$ で, \
  $q divides.not phi^j (n)$ かつ $q | phi^j (m)$ を満たすものが存在する.
] <supplylemma>

#[

#set text(size: 9pt)

$phi(n)$ は各 $p^e || n$ について $p^(e-1)(p-1)$ の積である.

つまり, $phi$ を繰り返し適用するにつれて基本的に $p$ の指数は0に達するまで1ずつ減っていき, それが成り立たないのは $p | q-1$ を満たす素数 $q$ が因数のとき.

ここで"供給"される $p$ のべきは $q$ の指数によらない.

いまの設定では, 最初 $p | n, p divides.not m$ で $m$ より $n$ のほうが $p$ を多く含んでいたにも関わらず, $i$ 回 $phi$ を適用したらそれが入れ替わった.

ということは, どこかで $phi^j (n)$ には含まれない $q$ が $phi^j (m)$ に含まれており, その $q$ が $p$ (のべき) を $m$ 側に供給したに違いない, というのが筆者の考えるこの補題の感覚的な説明である.

]

#proof[
  背理法で示す.

  つまり, すべての素数 $q>p$ と $0<=j<i$ を満たす $j$ について $q | phi^j (m)$ ならば $q | phi^j (n)$ を仮定する.

  このとき, すべての $0<=j<=i$ について $nu_p (phi^j (n))>=nu_p (phi^j (m))$ が成り立ってしまうことを帰納法で示す.

  まず, $j=0$ のときは $p | n, p divides.not m$ から $nu_p (phi^j (n))>=1, nu_p (phi^j (m))=0$ よりよい.

  次に, $0<=j=k<i$ のとき $nu_p (phi^k (n))>=nu_p (phi^k (m))$ を仮定しよう. (目標は, $nu_p (phi^(k+1) (n))>=nu_p (phi^(k+1) (m))$ を示すことである.)

  このとき, @nu_p_phi より $display(nu_p (phi^(k+1)(n))=max(0, nu_p (phi^k (n))-1)+sum_(r>p,r | phi^k (n))nu_p (r-1))$.

  (ただし $r$ は素数を指す.)

  同様の変形が $nu_p (phi^(k+1) (m))$ についてもできるので, 

  1. $display(max(0, nu_p (phi^k (n))-1)>=max(0, nu_p (phi^k (m))-1))$
  2. $display(sum_(r>p,r | phi^k (n)) nu_p (r-1)>=sum_(r>p,r | phi^k (m)) nu_p (r-1))$

  のふたつを示すことができれば, $nu_p (phi^(k+1) (n))>=nu_p (phi^(k+1) (m))$ がそこから導かれる.

  1の証明: #indentbox[
    簡単のため, $nu_p (phi^k (n))=x, nu_p (phi^k (m))=y$ とおいてしまおう. ($x, y$ は非負整数.)

    すると, 2は $display(max(0, x-1)>=max(0, y-1))$ と同じことである.

    いま帰納法の仮定より $nu_p (phi^k (n))>=nu_p (phi^k (m))$ から, $x>=y$.

    よって $x>=1$ かつ $y=0$, $x>=1$ かつ $x>=y>=1$, $x=0$ かつ $y=0$ の3つの場合分けができて, 

    それぞれについて上の不等式が成り立つことは簡単な計算と考察によって確かめられる.
  ]

  2の証明: #indentbox[
    背理法の仮定より, すべての素数 $q>p$ と $0<=j<i$ を満たす $j$ について $q | phi^j (m)==>q | phi^j (n)$.

    したがって, $r>p$ を満たす $phi^k (n)$ の素因数の集合は $r>p$ を満たす $phi^k (m)$ の素因数の集合のsupersetである.

    よって, $display(sum_(r>p, r | phi^k (n))nu_p (r-1)>=sum_(r>p, r | phi^k (m))nu_p (r-1))$.
  ]

  以上より, $nu_p (phi^(k+1) (n))>=nu_p (phi^(k+1) (m))$ が示せたので, 帰納法よりすべての $0<=j<=i$ について $nu_p (phi^j (n))>=nu_p (phi^j (m)).$

  特に $j=i$ の場合 $nu_p (phi^i (n))>=nu_p (phi^i (m))$ だが, これは $p divides.not phi^i (n), p | phi^i (m)$ というもとの設定に矛盾.

  したがって背理法より, ある素数 $q>p$ と $0<=j<i$ を満たす整数 $j$ で, $q divides.not phi^j (n)$ かつ $q | phi^j (m)$ を満たすものが存在する.
]

#theorem[
  $n, m, k$ を正整数とする. $display((phi^k (n))/n=(phi^k (m))/m ==> rad(n)=rad(m))$.
]

#proof[
  @multiphi-equivalent-condition より,

  $ rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m)) quad ... (*) $ 
  
  から $rad(n)=rad(m)$ を導くことができればよい.

  いま, $k=1$ の場合は明らかなので $k>1$ の場合を考える.

  背理法で示す; つまり, $rad(n) eq.not rad(m)$ と補題の式を仮定して, 矛盾を示す.

  ここで, 命題「任意の素数 $p$ と $i<k$ を満たす非負整数 $i$ について, $(p | phi^i (n))⊻(p | phi^i (m))$ ならば, ある $p$ より大きい素数 $q$ と $i'<k$ を満たす非負整数 $i'$ で, $(q | phi^(i') (n))⊻(q | phi^(i') (m))$ を満たすものが存在する」(命題Aと呼ぶことにする)を証明する.

  なお, $⊻$ は排他的論理和を表す; つまり, $p ⊻ q <--> (p and not q) or (not p and q)$.

  #proof[
    排他的論理和は交換するので, 一般性を失わずに $p | phi^i (n), p divides.not phi^i (m)$ を仮定できる.

    式 $(*)$ の両辺の $nu_p$ をとると, $display(sum_(x=0)^(k-1)nu_p (rad(phi^x (n)))=sum_(x=0)^(k-1)nu_p (rad(phi^x (m))))$ を得る.

    しかし, $p | phi^i (n)$ より $nu_p (rad(phi^i (n)))=1$, $p divides.not phi^i (m)$ より $nu_p (rad(phi^i (m)))=0$.

    したがって, $nu_p (rad(phi^i (n)))>nu_p (rad(phi^i (m)))$ であるから, $display(sum_(0<=x<k, x eq.not i)nu_p (rad(phi^x (n)))<sum_(0<=x<k, x eq.not i)nu_p (rad(phi^x (m))))$ が成り立つ.

    よって, ある $k$ 未満の $i$ と等しくない非負整数 $j$ で, $nu_p (rad(phi^j (n)))<nu_p (rad(phi^j (m)))$ を満たすものが存在する.

    しかし, 一般の $n$ について $rad(n)$ は無平方数であることから, $display(nu_p (rad(n))=cases(0 quad "if" p divides.not n\,, 1 quad "if" p | n.))$

    よって, $p divides.not phi^j (n), p | phi^j (m)$.

    ここで $i eq.not j$ より $i<j$ もしくは $j<i$ のどちらかが成り立つ.

    (1) $i<j$ の場合 #indentbox[
      $p divides.not phi^j (n), p | phi^j (m)$ を $p divides.not phi^(j-i) (phi^i (n)), p | phi^(j-i) (phi^i (m))$ と書けば, \
      @supplylemma に $n<-phi^i (n), m<-phi^i (m), i<-j-i$ として代入することで, \
      ある素数 $q>p$ と $0<=i'<j-i$ を満たす整数 $i'$ で, $q divides.not phi^(i') (phi^i (n))$ かつ $q | phi^(i') (phi^i (m))$ を満たすものが存在することがわかる.

      $i'$ を $i'+i$ と置き直せば, $i'<j<k$ かつ $q divides.not phi^(i') (n), q | phi^(i') (m)$ が成り立つので, $(q | phi^(i') (n))⊻(q | phi^(i') (m))$ が成り立つ例が構成できた.
    ]

    (2) $j<i$ の場合 #indentbox[
      この場合も @supplylemma に代入する順番を変えるだけで, ほぼ同じ議論である.

      $p | phi^i (n), p divides.not phi^i (m)$ を $p divides.not phi^(i-j) (phi^j (m)), p | phi^(i-j) (phi^i (n))$ と書けば,\
      @supplylemma に $n<-phi^j (m), m<-phi^j (n), i<-i-j$ として代入することで, \
      ある素数 $q>p$ と $0<=i'<i-j$ を満たす整数 $i'$ で, $q divides.not phi^(i') (phi^j (m))$ かつ $q | phi^(i') (phi^j (n))$ を満たすものが存在することがわかる.

      $i'$ を $i'+j$ と置き直せば, $i'<i<k$ かつ $q | phi^(i')(n), q divides.not phi^(i')(m)$ が成り立つので, この場合も $(q | phi^(i')(n))⊻(q | phi^(i')(m))$ が成り立つ例が構成できた. 
    ]
  ]

  さて, 命題Aを用いると, 命題「任意の素数 $p$ と $i<k$ を満たす非負整数 $i$ と正整数 $X$ について, $(p | phi^i (n))⊻(p | phi^i (m))$ ならば, ある $X$ より大きい素数 $q$ と, $i'<k$ を満たす非負整数 $i'$ で, $(q | phi^(i')(n))⊻(q | phi^(i')(m))$ を満たすものが存在する」(命題Bと呼ぶ) を示すことができる.

  #proof[
    $X$ に対する帰納法で示す.

    $X=1$ の場合は, 素数は $1$ より大きいので命題Aから直接従う.

    $X$ のとき命題Bが成り立つと仮定すると, 帰納法の仮定から $X$ より大きい素数 $q_0$ と, $i'_0<k$ を満たす非負整数 $i'_0$ で, $(q_0 | phi^(i')(n))⊻(q_0 | phi^(i')(m))$ を満たすものが存在する.

    命題A に $p<-q_0, i<-i'_0$ を代入すれば, $q_0$ より大きい素数 $q$ と, $i'<k$ を満たす非負整数 $i'$ で, $(q | phi^(i')(n))⊻(q | phi^(i')(m))$ を満たすものが存在する.

    この $q$ は, $X<q_0<q$ より, $X+1<q$ を満たし, したがって $X+1$ のときも命題Bが成り立つ.
  ]

  さて, この命題Bは適用できてはならない.

  もしある素数 $p$ と $i<k$ を満たす非負整数 $i$ について, $(p | phi^i (n))⊻(p | phi^i (m))$ が成り立つならば, $X$ にはどんな巨大な数も当てはめられるからである.

  例えば, $(q | phi^(i')(n))⊻(q | phi^(i')(m))$ は $display(q | product_(x=0)^(k-1){phi^x (n)phi^x (m)})$ を導くので, $display(X=product_(x=0)^(k-1){phi^x (n)phi^x (m)})$ とすれば $q$ が $X$ より大きいというのは矛盾だからである.

  したがって, すべての素数 $p$ と $i<k$ を満たす非負整数 $i$ について, $p | phi^i (n) <--> p | phi^i (m)$ が成り立っていなければならない.

  特に $i=0$ とすれば $p | n <--> p | m$ から, $n$ と $m$ の素因数は等しく, したがって $rad(n)=rad(m)$ である.
]

= 強い条件

さて, $display((phi^k (n))/n=(phi^k (m))/m ==> rad(n)=rad(m))$ が先の定理の結論であったが, $k>1$ の場合, 逆は必ずしも成り立たない.

つまり, $rad(n)=rad(m)$ は弱い条件である.

より強い条件についても考察することができる:

いま, 正整数 $n, i$ について $nu_p (n)=i$ を満たす素数 $p$ 全体の集合を $S_i (n)$, $nu_p (n)>=i$ を満たす素数 $p$ 全体の集合を $S_(>=i)(n)$ とおく.

#definition[
  $n, m, k$ を正整数とする.

  すべての $1<=i<k$ の範囲の整数 $i$ について $S_i (n)=S_i (m)$ が成り立ち, かつ $S_(>=k)(n)=S_(>=k)(m)$ であることを $n~_k m$ と書き, $n$ と $m$ は $k$ 同値であるという.
]

#lemma[
  $n~_k m$ ならば, すべての $1<=k'<k$ の範囲の整数 $k'$ について $n~_k' m$.
] <higher-level-stronger>

#proof[
  任意の1より大きい整数 $k$ について $n~_k m --> n~_(k-1) m$ が言えれば十分なので, 以下これを示す.

  $n~_k m$ を仮定すれば, $n~_(k-1) m$ の定義の前の部分「すべての $1<=i<k-1$ の範囲の整数 $i$ について $S_i (n)=S_i (m)$」は明らかであろう.

  一方, $S_(>=k-1)(n)=S_(k-1) (n)union S_(>=k)(n)$ より, $n~_k m$ を仮定すれば $S_(>=k-1)(n)=S_(>=k-1)(m)$ も成り立つ.
]

#theorem[
  $n, m, k$ を正整数とする. $n~_k m$ ならば $n~_(phi^k) m$.
]

#proof[
  @multiphi-equivalent-condition より, $n~_k m --> rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m))$ を示せばよい.

  これは命題「任意の正整数 $n, m, k$ について $n~_k m$ ならば $rad(phi^(k-1)(n))=rad(phi^(k-1)(m))$」(命題Aと呼ぶことにする) がいえれば十分である.

  なぜなら命題Aが成り立てば, @higher-level-stronger より, $n~_(k-1) m, n~_(k-2) m, ..., n~_1 m$ と合わせて $rad(n)=rad(m), rad(phi(n))=rad(phi(m)), ..., rad(phi^(k-1)(n))=rad(phi^(k-1)(m))$ が成り立つからである.

  そして, 命題Aを示すには, 命題「任意の正整数 $n, m, k smallspace (k>1)$ について $n~_k m$ ならば $phi(n)~_(k-1)phi(m)$」(命題Bと呼ぶことにする) がいえれば十分である.

  なぜなら 命題Bが成り立てば, $n~_k m$ の仮定から $phi(n)~_(k-1)phi(m), phi^2(n)~_(k-2)phi^2(m), ...$ と順に示していって $phi^(k-1)(n)~_1phi^(k-1)(m)$ までが言えるが, 一般に $x>=1$ について @higher-level-stronger より $~_x$ は $~_1$ を含み, また $n~_1 m$ は $rad(n)=rad(m)$ と同じ意味だからである.

  よって命題Bを示す.

  つまり, $n, m, k>1$ を正整数, $n~_k m$ を仮定したときに, $phi(n)~_(k-1)phi(m)$ をいう.

  さて, $phi(n)~_(k-1)phi(m)$ とはすべての $1<=i<k-1$ の範囲の整数 $i$ について $S_i (phi(n))=S_i (phi(m))$ かつ $S_(>=k-1)(phi(n))=S_(>=k-1)(phi(m))$ ということであるが, いま条件は $n, m$ に対して対称であるから, すべての $1<=i<k-1$ の範囲の整数 $i$ について $S_i (phi(n))subset S_i (phi(m)) quad ...(1)$ かつ $S_(>=k-1)(phi(n))subset S_(>=k-1)(phi(m)) quad ...(2)$ を示せば十分である.

  (1) の証明: #indentbox[
    $S_i (phi(n))subset S_i (phi(m))$ とは, 任意の素数 $p$ について $p in S_i (phi(n))-->p in S_i (phi(m))$ ということで, つまり $nu_p (phi(n))=i-->nu_p (phi(m))=i$ ということである.

    これが任意の $1<=i<k-1$ の範囲の整数 $i$ について成り立っていることを示したい.

    そのためには, $nu_p (phi(n))<k-1-->nu_p (phi(n))=nu_p (phi(m))$ が言えればよい.

    @nu_p_phi の結果を再掲すると, $display(nu_p (phi(n))=max(0, nu_p (n)-1)+sum_(q>p,q | n)nu_p (q-1))$.

    いま, $n~_k m$ より $n~_1 m$, つまり $rad(n)=rad(m)$ が成り立っているので, $n$ の素因数全体の集合と $m$ の素因数全体の集合は等しい.

    したがって, $display(sum_(q>p,q | n)nu_p (q-1)=sum_(q>p,q | m)nu_p (q-1))$ が成り立つので, $max(0, nu_p (n)-1)=max(0, nu_p (m)-1)$ が言えればよい.

    ところが, $max(0, nu_p (n)-1)<=nu_p (phi(n))<k-1$ より $nu_p (n)<k$.

    $nu_p (n)=0$ のときは, $rad(n)=rad(m)$ より $p divides.not m$, したがって $nu_p (m)=0$ なので $nu_p (n)=nu_p (m)$.

    それ以外のときも, $n~_k m$ より, $p in S_(nu_p (n))(n)=S_(nu_p (n))(m)$ から, $nu_p (n)=nu_p (m)$ が成り立ち, よって式 (1) は証明された.
  ]

  (2) の証明: #indentbox[
    $S_(>=k-1)(phi(n))subset S_(>=k-1)(phi(m))$ とは, 任意の素数 $p$ について $p in S_(>=k-1)(phi(n))-->p in S_(>=k-1)(phi(m))$ ということで, つまり $nu_p (phi(n))>=k-1-->nu_p (phi(m))>=k-1$ ということである.

    先ほどの議論から, $display(sum_(q>p,q | n)nu_p (q-1)=sum_(q>p,q | m)nu_p (q-1))$ で, これを $X$ とおこう.

    すると, $max(0, nu_p (n)-1)>=k-X-1 --> max(0, nu_p (m)-1)>=k-X-1$ が示したい問題になる.

    もし $nu_p (n)<k$ であれば, $n~_k m$ より $nu_p (n)=nu_p (m)$ が先の議論から成り立つので, 上式はただちに成り立つ.

    よって, $nu_p (n)>=k$ の場合を考える.

    このとき, $n~_k m$ より, $p in S_(>=k)(n)=S_(>=k)(m)$ から, $nu_p (m)>=k$ が成り立つ.

    $k>1$ より, $max(0, nu_p (m)-1)=nu_p (m)-1$ で, これが $k-1$ 以上, よって $X>=0$ から $k-X-1$ 以上であることがわかる.
  ]
]

#set heading(numbering: none)

= リンク

GitHub にアップロードされた本論文のリンク: #link("https://github.com/hikaru-kajita/mathematics/blob/main/multiphi-equivalence/multiphi-equivalence.pdf")
