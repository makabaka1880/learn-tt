#import "@preview/derive-it:1.1.0": *;
#set page(height: 2000pt)
#let ball = it => circle(radius: 0.3cm)[
    #set align(center + horizon); #it
]
#let blt = it => jt => {
    let left = ()
    let right = ()
    for i in it { left.push(ball(i)) }
    for j in jt { right.push(ball(j)) }
    pad(top: 3pt, bottom: 3pt, left: 3pt)[$#(left + ($<$,) + right).join()$]
}
#let bgt = it => jt => {
    let left = ()
    let right = ()
    for i in it { left.push(ball(i)) }
    for j in jt { right.push(ball(j)) }
    pad(top: 3pt, bottom: 3pt, left: 3pt)[$#(left + ($>$,) + right).join()$]
}
#let beq = it => jt => {
    let left = ()
    let right = ()
    for i in it { left.push(ball(i)) }
    for j in jt { right.push(ball(j)) }
    pad(top: 3pt, bottom: 3pt, left: 3pt)[$#(left + ($=$,) + right).join()$]
}

#ded-nat(arr: (
    ("I", 0, beq((2, 3, 4))((6, 7, 8, 9)), ""),
    ("II", 1, beq((2, 3, 4))((10, 11, 12)), "1号球"),
    ("II", 1, blt((2, 3, 4))((10, 11, 12)), ""),
    ("III", 2, beq((10,))((11,)), "12号球更重"),
    ("III", 2, blt((10,))((11,)), "11号球更重"),
    ("III", 2, bgt((10,))((11,)), "10号球更重"),
    ("II", 1, bgt((2, 3, 4))((10, 11, 12)), ""),
    ("III", 2, beq((10,))((11,)), "12号球更轻"),
    ("III", 2, blt((10,))((11,)), "10号球更轻"),
    ("III", 2, bgt((10,))((11,)), "11号球更轻"),
    ("I", 0, blt((2, 3, 4, 5))((6, 7, 8, 9)), ""),
    ("II", 1, beq((2, 6, 7))((3, 8, 9)), ""),
    ("III", 2, blt((4,))((5,)), "4号球更轻"),
    ("III", 2, bgt((4,))((5,)), "5号球更轻"),
    ("II", 1, blt((2, 6, 7))((3, 8, 9)), ""),
    ("III", 2, beq((8,))((9,)), "2号球更轻"),
    ("III", 2, blt((8,))((9,)), "9号球更重"),
    ("III", 2, bgt((8,))((9,)), "8号球更重"),
    ("II", 1, bgt((2, 6, 7))((3, 8, 9)), ""),
    ("III", 2, beq((6,))((7,)), "3号球更轻"),
    ("III", 2, blt((6,))((7,)), "7号球更重"),
    ("III", 2, bgt((6,))((7,)), "6号球更重"),
    ("I", 0, bgt((2, 3, 4, 5))((6, 7, 8, 9)), ""),
    ("II", 1, beq((6, 2, 3))((7, 4, 5)), ""),
    ("III", 2, blt((8,))((9,)), "8号球更轻"),
    ("III", 2, bgt((8,))((9,)), "9号球更轻"),
    ("II", 1, blt((6, 2, 3))((7, 4, 5)), ""),
    ("III", 2, beq((4,))((5,)), "6号球更轻"),
    ("III", 2, blt((4,))((5,)), "5号球更重"),
    ("III", 2, bgt((4,))((5,)), "4号球更重"),
    ("II", 1, bgt((6, 2, 3))((7, 4, 5)), ""),
    ("III", 2, beq((2,))((3,)), "7号球更轻"),
    ("III", 2, blt((2,))((3,)), "3号球更重"),
    ("III", 2, bgt((2,))((3,)), "2号球更重"),
))
