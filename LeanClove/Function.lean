namespace LeanClove

def identity (x : α) : α := x
def constantly (x : α) (_ : β) : α := x
def comp (f : β → γ) (g : α → β) (x : α) : γ := f (g x)
def «partial» (f : α → β → γ) (x : α) : β → γ := f x
def complement (p : α → Bool) (x : α) : Bool := !(p x)
def fnil (f : α → β) (fallback : α) (x : Option α) : β := f (x.getD fallback)
def juxt {α : Type u} {β : Type v} (fs : List (α → β)) (x : α) : List β := fs.map fun f => f x

@[simp] theorem comp_identity (f : α → β) : comp f identity = f := rfl
@[simp] theorem identity_comp (f : α → β) : comp identity f = f := rfl
theorem comp_assoc (f : γ → δ) (g : β → γ) (h : α → β) :
    comp (comp f g) h = comp f (comp g h) := rfl

@[simp] theorem constantly_apply (x : α) (y : β) : constantly x y = x := rfl
@[simp] theorem partial_apply (f : α → β → γ) (x : α) (y : β) :
    LeanClove.«partial» f x y = f x y := rfl

@[simp] theorem complement_complement (p : α → Bool) : complement (complement p) = p := by
  funext x
  simp [complement]

@[simp] theorem fnil_none (f : α → β) (fallback : α) : fnil f fallback none = f fallback := rfl
@[simp] theorem fnil_some (f : α → β) (fallback x : α) :
    fnil f fallback (Option.some x) = f x := rfl

@[simp] theorem length_juxt {α : Type u} {β : Type v} (fs : List (α → β)) (x : α) :
    (juxt fs x).length = fs.length :=
  List.length_map _

end LeanClove
