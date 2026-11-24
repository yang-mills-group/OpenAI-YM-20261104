import YM.RG11Proof.Jets.Pencil
/-!
# Changing the profile in a slot reading

For composition of width-preserving profile operations, e.g. Euler and
infinitesimal derivatives, with series frame transformations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical
open YM.PertExtension.Position PowerSeries Function YM.RG11.Jets

structure Keeper {P: Type*} (width:P→ℕ) where
  profile : P → P
  size (p:P): width p = width (profile p)
namespace Keeper
variable {J P R:Type*}{width:P→ℕ}(s t : Keeper width)

def move (v : Mark J width):Mark J width:=⟨s.profile v.1,v.2 ∘ Fin.cast (s.size v.1).symm⟩

def id (width:P→ℕ):Keeper width:=⟨_root_.id,fun _=>rfl⟩

def chain : Keeper width:= ⟨s.profile ∘ t.profile,fun p=> (t.size p).trans (s.size _)⟩

theorem move_id (v:Mark J width) : (id width).move v=v:= by rcases v with ⟨p,j⟩; rfl

theorem move_chain (v:Mark J width): s.move (t.move v)=(chain s t).move v:=rfl

theorem move_eq_self {v : Mark J width}(h:s.profile v.1=v.1):s.move v=v:=by
   cases v with | mk p j=>
   change @Sigma.mk _ (fun p=>Fin (width p) → J) (s.profile p) (j ∘ Fin.cast _) = Sigma.mk p j
   have aux (q:P)(k:width p=width q)(he:q=p): @Sigma.mk _ (fun p=>Fin (width p)→J) q (j ∘ Fin.cast k.symm)=Sigma.mk p j:=by
     subst q; rfl
   exact aux _ (s.size p) h

local notation "slots" => PertExtension.Position.insert

private theorem slot_cast [Fintype J] [CommSemiring R](a:Mark J width→R)(D:FrameAt J R) (p:P){m n:ℕ} (h:m=n)(k:width p=n) (j:Fin m→J):
  slots J width a D ⟨p,j ∘ Fin.cast (k.trans h.symm)⟩=
      ∑ b:Fin m→J,a ⟨p,b ∘ Fin.cast (k.trans h.symm)⟩ * ∏ i:Fin m, D (j i) (b i):=by
        subst m; subst n; rfl

theorem move_slot [Fintype J][CommSemiring R](a:Mark J width→R)(D:FrameAt J R)(v:Mark J width):
   slots J width a D (s.move v)=slots J width (a ∘ s.move) D v := slot_cast a D (s.profile _) (s.size v.1) rfl v.2

private theorem update_cast (p:P){n m:ℕ}(h:m=n)(k:n=width p)(j:Fin m→J)(i:Fin m)(b:J):
    ((Function.update j i b) ∘ Fin.cast (k.symm.trans h.symm)) = Function.update (j ∘ Fin.cast (k.symm.trans h.symm)) (Fin.cast (h.trans k) i) b :=by
  subst m; subst n; rfl

@[simp] theorem move_updated (v:Mark J width)(i:Fin (width v.1))(j:J):
    s.move (⟨v.1,Function.update v.2 i j⟩:Mark J width)=
    ⟨(s.move v).1,Function.update (s.move v).2 (Fin.cast (s.size v.1) i) j⟩:=by
      unfold move; congr 1; rw [update_cast (k:=rfl) (h:=s.size v.1) (s.profile v.1)]

theorem move_orbit [Fintype J] [CommRing R] (a:Mark J width→R)(D:Square J R)(v:Mark J width):
    orbit a (s.move v) D=orbit (a ∘ s.move) v D:=by
  rw [formula,formula,framePencil, framePencil, move_slot]
  rfl

theorem move_act [Fintype J][CommRing R](a:ArrayAt J R width)(d:Change R J)(v:Mark J width):
   d.act a (s.move v)=d.act (a ∘ s.move) v:=move_slot ..

end Keeper
end YM.RG11.Scale
