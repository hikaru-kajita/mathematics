#set document(date: none)

#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0"
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#set text(
  font: ("Harano Aji Gothic"),
  size: 7pt
)

#set par(leading: 0.6em, spacing: 0.7em)

#show heading: set text(size: 12pt)

#let page_margin = 1.5cm

#set page(
  paper: "a4",
  margin: page_margin,
  background: rect(
    width: 100% - page_margin,
    height: 100% - page_margin, 
    radius: 4%, 
    stroke: stroke(rgb("#4285f4"))),
  columns: 2,
)

#show math.equation.where(block: false): it => {
  if it.has("label") and it.label == <stop-equation-recursion> {
    it
  } else {
    [$display(it)$<stop-equation-recursion>]
  }
}

#let smallspace = [#h(4pt)];

#let highlight(body) = {
  set text(rgb("#4285f4"))
  [#body]
}

#place(
  top + center,
  scope: "parent",
  float: true,
  text(size: 20pt, weight: "bold")[オイラー関数の多重合成を計算するアルゴリズム]
)

#place(
  top + right,
  scope: "parent",
  float: true,
  [
    #text()[Crimson Global Academy 梶田 光]
    #v(10pt)
  ]
)

= 概要

オイラー関数 $phi(n)$ の研究では, オイラー関数を含む方程式の解を研究する.

特に最近はオイラー関数の多重合成 $phi^k (n):=underbrace(phi\(...phi, k "times")(n)...)$ についての研究が進み, これを含む方程式の解を数値計算によって求めたい場面が多い.

しかし, $phi^k (n)$ は乗法的関数ではないので, 一般的に知られている区間篩をそのまま適用することができない.

そこで今回, 3つのアイデアを含む新しいアルゴリズムを発見し, Rustで実装した.

以下, 正整数 $k, N$ を固定し, $1<=n<=N$ のすべての $n$ に対して $n$ の素因数分解と $phi(n), phi^2 (n), ..., phi^k (n)$ が(メモリマップを用いて)高速に取得できるようなLUTをディスク上に構築するアルゴリズムについて考える.

= 1. 部分分解とオイラー関数

前回の発表では部分分解というアイデアを提案した.

これは正整数 $n<=N$ に対して $n=p_0p_1...p_(m-1) smallspace (p_i:"prime", p_i<=p_(i+1)), i_0=max {0<=i<=m | product_(0<=j<i)p_j<=sqrt(N)}, i_1=max {i_0<=i<=m | product_(i_0<=j<i)p_j<=sqrt(N)}$ とおいたとき, $f_0=product_(0<=j<i_0)p_j, f_1=product_(i_0<=j<i_1)p_j, f_2=n/(f_0f_1)$ として $n=f_0f_1f_2$ という形に書き表す方法である.

これは区間篩内で計算量の大幅な悪化なしに計算することができる.

前回, このような表し方がメモリマップする区間を $O(sqrt(N))$ に抑えつつ素因数分解を取得するのに有用ということを示した.

しかし今回, これが $phi^k (n)$ を計算する際にも有用であることがわかった.

一般の $n, m$ について, $d=gcd(n, m)$ とすると $phi(n m)=phi(n)phi(m)d/phi(d)$ という公式がある.

しかしここで, $1<=phi(n)<=n$ が成り立つことはもちろん, $1<=phi(m)d/phi(d)<=m$ も成り立ち, さらにこれは自然数である.

したがって, $italic("totient_product")([alpha_0, alpha_1, alpha_2])=[phi(alpha_0), phi(alpha_1)d/phi(d), phi(alpha_2)d'/phi(d')] "where" d=gcd(alpha_0, alpha_1), d'=gcd(alpha_0alpha_1, alpha_2)$ のような関数を定義すれば, $alpha=alpha_0alpha_1alpha_2$ について $italic("totient_product")([alpha_0, alpha_1, alpha_2])=[alpha'_0, alpha'_1, alpha'_2], alpha'=alpha'_0alpha'_1alpha'_2$ とおいたとき $phi(alpha)=alpha'$ かつ各 $0<=i<=2$ について $alpha'_i<=alpha_i$ が成り立つ.

よって $sqrt(N)$ 以下のすべての $n$ について $phi(n)$ を計算しておけば, 任意の $f_0, f_1, f_2<=sqrt(N)$ を満たす $n=f_0f_1f_2$ について $[f_0, f_1, f_2]$ に先の関数 $f$ を繰り返し適用することによって $phi(n), phi^2 (n), ...$ を計算することができる.

= 2. $k=2$ の場合: 調和級数のオーダーと空間計算量の見積り

まず $k=2$, つまり $phi(n), phi^2 (n)$ までしか計算しなくてよい場合を考える.

$n=f_0(n)f_1(n)f_2(n)$ とおいたとき, $f_0(n), f_1(n), f_2(n)<=sqrt(N)$ ならば計算できることは先程示した.

$f_0(n), f_1(n)<=sqrt(N)$ は定義上成り立っているから, $f_2(n)>sqrt(N)$ の場合を考える.

前回示した定理より, $f_2(n)$ は素数であるから, $alpha=f_0f_1<=sqrt(N)$ とおくと $phi(n)=phi(alpha)(f_2(n)-1)$.

ここから $phi^2 (n)$ を計算するには $f_2(n)-1$ の分解の情報が必要である.

そこで, primechain という長さ $N$ の配列を用意する.

区間篩が $sqrt(N)<["start", "end"]$ の区間で実行されているとすると, primechainの $["start"/2, "end"/2], ["start"/3, "end"/3], ["start"/4, "end"/4], ..., ["start"/sqrt(N), "end"/sqrt(N)]$ の部分をメモリマップする. (この方法をharmonic mapと呼ぶことにする.)

$"start"<=n<="end"$ かつ $n$ が素数 (つまり$f_0(n)=f_1(n)=1$)であれば, $[f_0(n-1), f_1(n-1)]$ を$"primechain"[n]$ に記録する.

その後, $f_2(n)>sqrt(N)$ で関数 $f$ の繰り返しによって $phi^2 (n)$ を計算できない場合, $"primechain"[f_2(n)]$ から $[f_0(f_2(n)-1), f_1(f_2(n)-1)]$ を取得.

$f_2(f_2(n)-1)$ がそこから計算でき, これが $sqrt(N)$ 以下なら $phi(n)$ は $phi(alpha) dot f_0(f_2(n)-1) dot f_1(f_2(n)-1) dot f_2(f_2(n)-1)$ と $sqrt(N)$ 以下の正整数の積で表せる.

そうでなければ, $f_2(f_2(n)-1)$ は素数なので $phi(n)=phi(phi(alpha) dot f_0(f_2(n)-1) dot f_1(f_2(n)-1)) dot (f_2(f_2(n)-1)-1)$ と計算すればよい.

ここでメモリマップする範囲は調和級数の発散する速度より $O(("end"-"start")log N)$ 程度にしかならず, 区間の大きさを $sqrt(N)$ 程度にとれば全体を通しての空間計算量は $O(sqrt(N)log N)$ ですむ.

= 3. 一般の場合: primechainの繋げ方

まず, $n$ の分解 $n=f_0f_1f_2$ を考える.

もし $f_2<=sqrt(N)$ であれば, $[f_0, f_1, f_2]$ に $f$ を繰り返し適用し続ければよい.

それ以外の場合, $alpha=f_0f_1$ とおくと $alpha=n/f_2<N/sqrt(N)=sqrt(N)$ で, $phi(n)=phi(alpha f_2)=phi(alpha)(f_2-1)$ である.

$phi^2 (n)$ を計算するためには, $f_2-1$ の分解 $f_2-1=f'_0f'_1f'_2$ が必要である.

もし $f'_2<=sqrt(N)$ であれば, $phi(n)=phi(alpha)f'_0f'_1f'_2$ は $sqrt(N)$ 以下の正整数の積で書けるから $f$ を繰り返し適用すればよい.

それ以外の場合, $alpha'=phi(alpha)f'_0f'_1$ とおくと $k'=phi(n)/f'_2<n/sqrt(N)<=N/sqrt(N)=sqrt(N)$ で, $phi^2 (n)=phi(alpha')(f'_2-1)$.

$phi^3 (n)$ を計算するためには, $f'_2-1$ の分解 $f'_2-1=f''_0f''_1f''_2$ が必要である.

もし $f''_2<=sqrt(N)$ であれば, $phi^2 (n)=phi(alpha')f''_0f''_1f''_2$ は $sqrt(N)$ 以下の正整数の積で書けるから $f$ を繰り返し適用すればよい.

それ以外の場合, $alpha''=phi(alpha')f''_0f''_1f''_2$ とおくと $alpha''=(phi^2 (n))/f''_2<n/sqrt(N)<=N/sqrt(N)=sqrt(N)$ で, $phi^3 (n)=phi(alpha'')(f''_2-1)$.

$f'''$ を $f^((3))$, $f''''$ を $f^((4))$ などして表記すると, $phi^k (n)$ を計算するためには $f^((k-1))_0, f^((k-1))_1, f^((k-1))_2$ までが必要である.

ここで, $f_2^((i))$ は $n$ の約数ではないが, 実はある簡単に計算できる整数 $B_i=product_(m=1)^i f_0^((m))f_1^((m))$ を用いて $f_2^((i))=floor(n/B_i)$ と書けることが証明できる. (GPT-5との議論から発展.)

つまり, $f_2$ だけでなく $f'_2, f''_2, ...$ はすべてharmonic mapの範囲に含まれているから, primechainのharmonic mapを $f'_0, f'_1, f'_2, f''_0, f''_1, f''_2, ...$ を取得する目的に使うことができる.

#align(center)[
  #set text(size: 6pt)
  #diagram(
    debug: false,
    spacing: (20pt, 15pt),
    node-inset: 2pt,
    node((0, 0), $"primechain"[f_2]=(f'_0, f'_1)$, name: <pf0>),
    node((1, 0), $f'_2$, name: <f1>),
    node((3, 0), $"fallback to "italic("totient_product")$, name: <exit>),
    node((0, 1), $"primechain"[f'_2]=(f''_0, f''_1)$, name: <pf1>),
    node((1, 1), $f''_2$, name: <f2>),
    node((0, 2), $"primechain"[f''_2]=(f'''_0, f'''_1)$, name: <pf2>),
    node((1, 2), $f'''_2$, name: <f3>),
    node((0, 3), $"primechain"[f'''_2]=(f^((4))_0, f^((4))_1)$, name: <pf3>),
    node((1, 3), $f^((4))_2$, name: <f4>),
    node((0, 3.7), $dots.v$),
    node((1, 3.7), $dots.v$),

    edge(<pf0>, <f1>, "=>", label: $"calc"$,),
    edge(<f1>, <exit>, "->", label: $f'_2<=sqrt(N)$),

    edge(<f1>, ((), "|-", (<f1>, 50%, <pf1>)), ((), "-|", <pf1>), <pf1>, "->", label: $"otherwise"$, label-side: center),
    edge(<pf1>, <f2>, "=>", label: $"calc"$,),
    edge(<f2>, ((), "-|", <exit>), <exit>, "->", label: $f''_2<=sqrt(N)$, label-pos: 0.25),

    edge(<f2>, ((), "|-", (<f2>, 50%, <pf2>)), ((), "-|", <pf2>), <pf2>, "->", label: $"otherwise"$, label-side: center),
    edge(<pf2>, <f3>, "=>", label: $"calc"$),
    edge(<f3>, ((), "-|", <exit>), <exit>, "->", label: $f'''_2<=sqrt(N)$, label-pos: 0.25),

    edge(<f3>, ((), "|-", (<f3>, 50%, <pf3>)), ((), "-|", <pf3>), <pf3>, "->", label: $"otherwise"$, label-side: center),
    edge(<pf3>, <f4>, "=>", label: $"calc"$),
    edge(<f4>, ((), "-|", <exit>), <exit>, "->", label: $f^((4))_2<=sqrt(N)$, label-pos: 0.25),
  )
]

一般に $phi^k (n)=1$ となる最小の $k$ は $1+log_2 n$ であることが #cite(form: "prose", <pillai1929function>) によって示されているため, 実用上(オイラー関数の多重合成の性質を調べるという意味で)このアルゴリズムが使われるのは $k<=1+log_2 N$ の範囲のみである.

これを考慮すると, #highlight[全体の時間計算量は $O(k N log N)$, 空間計算量が $O(sqrt(N)log N)$, 消費するディスクの容量が $O(k N)$] となって, これは十分高速である.


= 最適化について

並列化とメモリマップの領域の最適化についても考察した.

特に後者については, primechainにアクセスするときの添字が素数であることから, wheel sieveの考え方を利用して空間計算量とディスクの容量を $log log N$ だけ落とすことができる.

= テスト

他にRAMに入らない範囲の $n$ の $phi^k (n)$ を計算するアルゴリズムが知られていないので, 既存のアルゴリズムとの速度比較はできない.

しかし, アルゴリズムの正当性のテストのため, RAMに入る範囲の $N=10^8, k=4$ で通常のエラトステネスの篩と比較し, $1<=n<=N$ の範囲で $phi(n)$ から $phi^4 (n)$ までの値がすべて一致することを確認した.

= 展望

今回のアルゴリズムはかなりオイラー関数固有の性質を活用しているため, 他に多重合成が研究されている乗法的関数 (約数の和関数など) にどこまで応用できるかはまだわかっていない.

また, 同じ問題を解くアルゴリズムで, 時間と空間のトレードオフなしにこのアルゴリズムの計算量を改善することはできないと予想するが, これを解決するのはとても難しいと思われる.

= リンク

- 論文: #link("https://github.com/hikaru-kajita/mathematics")

#bibliography("works.bib", style: "ieee", title: "参考文献")
