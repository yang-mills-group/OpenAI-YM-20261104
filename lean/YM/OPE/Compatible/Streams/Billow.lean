import YM.OPE.Compatible.Streams.Lab
/-! # ℐ prelude. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {d k i j m s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{w':V→ℝ}{p':Mints E}
local notation "F!"=> Fruition X (μ k)
variable (A:Aeon V T X w')(K:Eave L X T a r x u k)
lemma bolt (hq:0<μ k) : (Fleet X (μ k) s hq)^i *portC X (μ k) s ^ i=1 ∧portC X (μ k) s ^ i * (Fleet X (μ k) s hq)^i=1:=by
    have hs:= wineP (m:=s) X hq; let f:=Fleet X (μ k) s hq; let g:=portC X (μ k) s; have ht:Commute f g:= hs.1.trans hs.2.1.symm
    constructor; · rw [← ht.mul_pow,hs.1,one_pow]
    rw [← ht.symm.mul_pow,hs.2.1,one_pow]
lemma timeK (hp:0 < μ k):Injective ((Fleet X (μ k) s hp)^m):=(show LeftInverse (fun i=> (portC X (μ k) s^m) i) (fun i=> ((Fleet X (μ k) s hp)^m) i) from fun x=> DFunLike.congr_fun ((bolt (X:=X) (s:=s) hp).2) x).injective -- s argument
-- Ƒ tilt.Hν. Preserves leading on any ζ.Diag port
include K
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
omit [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)] in
lemma PursArc {i:Fin s}{p:Fruition X (μ k)}(z:ℕ)(h:trims i.val p.val): trims i.val ((portC X (μ k) s^z) p).val ∧ (T i).Tap k (((portC X (μ k) s^z) p).val i)= μ k^z • (T i).Tap k (p.val i):=by
      rw [portables]; have hz:= phaseLeaf T K.HB K.mark i p.val p.property h; induction z with
      | zero=> simp only [pow_zero,one_smul]; exact ⟨h,rfl⟩
      | succ z ih=>
          let g:=p.val; rw [pow_succ',byway]; let f:Fruition X (μ k):=(portC X (μ k) s^z) p; have hp:(X^z) g=f.val:= (portables ..).symm; have ht: (X^z) g ∈ Fruition X (μ k):=hp.symm ▸ f.property
          have hX:(X^z) g i∈ (T i).flag k:= phaseLeaf T K.HB K.mark i _ ht ih.1
          refine ⟨K.HB.arum _ _ ih.1, ?_⟩; rw [scissor K.HB.arum i ((X^z) p.val) ih.1,(K.HB.gait i).tempo k K.mark _ hX,ih.2,pow_succ', mul_smul]
lemma PursBack (hq:0<μ k){i:Fin s}(p:Fruition X (μ k))(z:ℕ)(h:trims i.val p.val):
    let v:=(Fleet X (μ k) s hq^z) p; trims i.val v.val∧ (μ k)^z • (T i).Tap k (v.val i)=(T i).Tap k (p.val i):=by
      intro v; have he:(portC X (μ k) s^z) v=p:= DFunLike.congr_fun ((bolt hq).2) p
      have hx(n:ℕ)(hk:n ≤ i.val): trims n v.val:=by
           induction n with
           | zero=> exact trims.be _
           | succ n ih=>
               have ht:= ih (by omega); let j:Fin s:=⟨n,by have he:i.val<s:=i.isLt;omega⟩; have hv:= (PursArc K (i:=j) z (p:=v) ht).2; rw [he,h j hk,map_zero,eq_comm,smul_eq_zero_iff_right (pow_pos hq z|>.ne')] at hv
               apply (K.Vita (n+1) (hk.trans i.isLt.le)).1; intro k hk'; by_cases hp:k=j; · subst k; exact hv
               exact (K.Vita n (Nat.le_of_lt j.isLt)).2 ht k (Nat.lt_of_le_of_ne (by omega) (fun hh=>hp (Fin.ext hh))) -- casts
      exact ⟨hx _ le_rfl,(show (T i).Tap k (p.val i)=_ from he ▸ (PursArc K z (p:=v) (hx _ le_rfl)).2).symm⟩
end YM.OPE.Hark
