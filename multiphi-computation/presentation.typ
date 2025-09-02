#import "@preview/cades:0.3.0": qr-code

#let smallspace = [#h(4pt)];
#let even = [even];
#let odd = [odd];
#let prime = [prime];
#let rad = [rad];
#let cophi = [co$φ$];

#set page(
  paper: "presentation-16-9",
  footer: layout(size => [
    #rect(
      fill: blue.lighten(95%),
      width: 100%,
      height: 100%,
      inset: 0pt,
      outset: (x: (page.width - size.width) / 2)
    )[
      #set text(size: 15pt)
      #set align(horizon)

      Hikaru Kajita
      #h(1fr)
      #counter(page).display(
        "1/1",
        both: true,
      )
    ]
  ])
)

#set text(
  lang: "ja",
  font: "Harano Aji Gothic",
  size: 16pt,
)

#show link: underline

#show math.equation: set text(font: ("New Computer Modern Math", "Harano Aji Mincho"))
#show math.equation: it => h(0.25em, weak: true) + it + h(0.25em, weak: true)

#show heading.where(level: 1): set text(size: 50pt)
#show heading.where(level: 2): set text(size: 35pt)
#show heading.where(level: 2): it => it + v(25pt)

#let customenv(id, description) = {
  let counter = counter("customenv-" + id)
  return (counter_step: true, body) => [
    #if counter_step {
      counter.step()
    }
    #block(
      fill: blue.lighten(80%),
      outset: 9pt,
      radius: 9pt,
      width: 100%,
      [
        #strong[#description #context {counter.display()}: #h(10pt)]
        #body
      ]
    )
  ]
}

#let theorem = customenv("theorem", "定理")
#let definition = customenv("definition", "定義")

#let proof(continuing: false, finished: true, body) = [
  #block(
    fill: blue.lighten(90%),
    outset: 9pt,
    radius: 9pt,
    width: 100%,
    [
      #if not continuing [_Proof._ #h(7pt)]
      #body
      #if finished [#h(1fr) $qed$]
    ]
  )
  #v(15pt)
]

#page(footer: none, background: none, [
  #set align(center + horizon)
  = オイラー関数の多重合成を計算するアルゴリズム #v(20pt)
  梶田光
])

#page[
  == 内容

  3つのアイデアの(ポスターや論文で伝えきれない)"気持ち"について


  1. 部分分解とオイラー関数
  2. $k=2$ の場合: 調和級数のオーダーと空間計算量の見積り
  3. 一般の場合: primechainの繋げ方
]

#page[
  == 1. 部分分解とオイラー関数

  部分分解は競技プログラミングでよく使われる "平方分割" のアイデアから.

  - 素因数分解をすべて書き下して計算するのは時間がかかる
  - 一般の $n$ について $phi(n)$ を配列から取得するには必要な空間が大きすぎる

  $sqrt(N)$ ギリギリまで素因数の積を順番に $f_0, f_1$ に詰め込むというアルゴリズムが時間と空間のトレードオフを現実的な範囲に落とし込む.

  そして, この方法は $n$ の素因数がすべて $sqrt(N)$ 以下であるときの $phi^k (n)$ の計算に応用できる.
]

#page[
  == 2. $k=2$ の場合: 調和級数のオーダーと空間計算量の見積り

  $k=2$ のケースから考えたのは初等整数論の研究の方でまず $phi^2 (n)$ について考えていたから.

  $n$ が($sqrt(N)$より)大きな素数の倍数であった場合の $phi^2 (n)$ の処理が難しいが, \
  調和級数 $display(H_n=sum_(k=1)^n 1/k~log n)$ を考えると $sqrt(N)$ 程度の長さの区間 $["start", "end"]$の中の $n$ の \
  $sqrt(N)$ より大きい素因数が含まれている可能性のある区間 $display(["start"/2, "end"/2]\, ["start"/3, "end"/3]\, ...\, ["start"/sqrt(N), "end"/sqrt(N)])$ を \
  すべてメモリにマップしてしまっても空間計算量は $O(sqrt(N)log N)$ と小さい. (harmonic map)
]

#page[
  == 3. 一般の場合: primechainの繋げ方

  一般の $k$ では, $phi^k (n)$ の計算のために

  - $f_2>sqrt(N)$ ならば $f'_0, f'_1$
  - さらに $f'_2>sqrt(N)$ ならば $f''_0, f''_1$
  - さらに $f''_2>sqrt(N)$ ならば $f'''_0, f'''_1$
  - $dots.v$

  という数列を最大 $k-1$ まで取得する必要がある.

  => 数列 $f_2, f'_2, f''_2, ...$ はすべて harmonic map の範囲内. (GPT-5との議論から発展.)

  => ディスク容量 $O(k N)$, 空間計算量 $O(sqrt(N)log N)$ で計算ができる.

  \

  このとき, primechainは連結リストに似たデータ構造から構成された巨大な森になっている.
]

#page[
  == 詳細な議論

  #qr-code("https://github.com/hikaru-kajita/mathematics/tree/main/multiphi-computation")

  #link("https://github.com/hikaru-kajita/mathematics/tree/main/multiphi-computation")
]

#page(footer: none, background: none)[
  #align(center + horizon)[
    #text(size: 40pt)[
      Thank you!
    ]
  ]
]
