import YM.MS.Local.Occupation

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
open Woven
variable {G: Gauge} {f: Grade G} {F: Law G} {h: ℤ} {r: ℕ}
namespace Woven
def Carry (G:Gauge) (h:ℤ) (r:ℕ):= Submodule.span ℂ {F:Law G| ∃ (f: Fin r→ Grade G) (w: Fin r→ℤ),(∀ i, f i∈ yields (w i) 0∧ Q (f i)=0)∧ (∑ i,w i)=h ∧ line r f=F}
lemma fare (G:Gauge) (h:ℤ) (r:ℕ): Carry G h r≤ Bed G h 0 r:= by
   rw [Carry,span_le]; rintro v ⟨p,w,f,h,rfl⟩
   apply SetLike.mem_coe.mpr
   convert! tileCub.mpr (line_in _ _ (fun i=> seedStar.mp (f i).1)) using 2 <;> simp [h]
lemma tensor_pure (p : Fin r→ Grade G) (w : Fin r→ℤ) (h: ∀ i, p i∈ yields (w i) 0 ∧ Q (p i)=0): natQ (line r p)=0:= by
    induction r with
    | zero=> exact no Gof
    | succ r ih=> change Gof.Q _=_; rw [line_bud,parity_bud (h 0).1, show MatrixLet.one Gof (p 0)=0 from (h 0).2,show Gof.Q (line r (p ∘ Fin.succ))=0 from ih _ (fun i=> w i.succ) (fun i=>(h i.succ))]; simp [← place_at]
lemma carry_pure (hf:F∈ Carry G h r): natQ F=0:= by
    suffices hp : Carry G h r ≤ LinearMap.ker natQ from hp hf
    rw [Carry,span_le]; rintro v ⟨p,w,f,h,rfl⟩; exact SetLike.mem_coe.mpr (LinearMap.mem_ker.mpr (tensor_pure p w f))
abbrev sym (F:Law G):= Koszul.Symm (field Landau.parity) F
end Woven
end YM.MS.Local.BV
