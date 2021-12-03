#! https://zhuanlan.zhihu.com/p/430229499

# Coq集合论讲座（appx.1 符号表）

> [GitHub - choukh/Baby-Set-Theory](https://github.com/choukh/Baby-Set-Theory)  
> Q群：893531731

```Coq
Scope 集合域

"x ∈ y" := (属于 x y)
"x ∉ y" := (not (属于 x y))
"a ⋸ b" := (or (属于 a b) (eq a b))

"A ⊆ B" := (包含 A B)
"A ⊈ B" := (not (包含 A B))
"A ⊂ B" := (and (包含 A B) (not (eq A B)))
"A ⊄ B" := (not (and (包含 A B) (not (eq A B))))

"{ x ∊ A | P }" := (分离 A (fun x => P))
"{ F | x ∊ A }" := (替代 (fun x => F) A)
"{ a , b }" := (配对 a b)
"{ a , }" := (单集 a)
"⋃ A" := (并集 A)
"'ℙ' A" := (幂集 A)

"⋂ A" := (交集 A)
"A - B" := (补集 A B)
"A ∪ B" := (二元并 A B)
"A ∩ B" := (二元交 A B)

"a ⁺" := (后继 a)

"< a , b , .. , c >" := (序偶 .. (序偶 a b) .. c)
"{ ' < a , b > ∊ A | P }" := (序偶分离 A (fun a b => P))
"A × B" := (直积 A B)

"f [ x ]" := (应用 f x)
"f : A ⇒ B" := (映射 f A B)
"f : A ⇔ B" := (单射 f A B)
"f : A ⟹ B" := (满射 f A B)
"f : A ⟺ B" := (双射 f A B)

"A ⟶ B" := (函数空间 A B)
"f ↾ A" := (限制 f A)
"F ↑ A" := (类函数限制 F A)

"x ⋵ C" := (类属于 x C)
"C ⫃ D" := (forall x (_ : 类属于 x C), 类属于 x D)
"A ⪽ C" := (forall x (_ : 属于 x A), 类属于 x C)

Scope 自然数算术域
Delimiting key is ω
"n + m" := (加法 n m)
"n * m" := (乘法 n m)
"n ^ m" := (幂运算 n m)

Scope 序数算术域
Delimiting key is ord
"α + β" := (加法 α β)
"α * β" := (乘法 α β)
"α ^ β" := (幂运算 α β)
```
