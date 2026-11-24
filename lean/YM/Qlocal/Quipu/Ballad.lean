import YM.Qlocal.Quipu.Recite
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
-- extend wall across both legs. χ preserves quiet.𝒮
open Tender Turbin Lasso
namespace Ballad
-- Film: number slip positions using fee support.
structure Tune (α:Type) where
    fee : ℕ→ℝ
    slip : ℕ→ Slip (Point α)
namespace Tune
omit [DecidableEq α]
abbrev typeR (Q:Tune α): Ink.Field α:=⟨ℕ,Q.fee,Q.slip⟩
variable (Q: Ink.Field α)(h:Q.Good a b k)(ha:0<a)
include h ha
lemma tuned : ∃ f:Tune α, (typeR f).Good a b k ∧ ∀ n,(typeR f).table n=Q.table n:= by
 letI:= (Ink.Field.cash ha.le h).countable_support.toEncodable; let X:= Function.support Q.fee; let F: ↑(Function.support Q.fee) ↪ ℕ:= ⟨_,Encodable.encode_injective⟩
 let f:Tune α:= ⟨Function.extend F (fun x=>Q.fee x.val) 0,Function.extend F (fun x=> Q.slip x.val) (fun _=>[])⟩; let G:=typeR f
 have he(x): f.fee (F x)= Q.fee x.val:= F.injective.extend_apply (fun x=> Q.fee x.val) (0:ℕ→ℝ) x; have hf(x): f.slip (F x)= Q.slip x.val:=F.injective.extend_apply (fun x=> Q.slip x.val) (fun _=>[]) x
 have hg(i:ℕ)(hi:i∉ Set.range F): f.fee i=0 ∧ f.slip i=[]:= ⟨extend_apply' (f:=⇑F) (fun x=> Q.fee x.val) (0:ℕ→ℝ) _ hi, extend_apply' (f:=⇑F) (fun x=> Q.slip x.val) (fun _=>[]) _ hi⟩
 have ht(x): G.price a (F x)=Q.price a x.val:= by unfold Ink.Field.price G typeR; dsimp only; rw [he,hf] -- unfold f dot
 have hh: SumBudget ((G.price a) ∘ F) b:= by rw [show (G.price a) ∘ F= _ from funext ht]; exact sumBudget_subtype _ h.pay
 refine ⟨f,⟨fun i=>?_, sumBudget_pass F (G.price a) hh (fun i H=>?_)⟩,fun v=>?_⟩ -- arg order
 · by_cases hp: i∈ Set.range F; · obtain ⟨x,rfl⟩:=hp; change List.length (f.slip _)≤ _; rw [hf]; exact h.length _
   change (f.slip i).length ≤ _; rw [(hg i hp).2]; exact Nat.zero_le _
 · unfold Ink.Field.price; rw [show G.fee i=_ from (hg i H).1,abs_zero,mul_zero]
 ext1 x; rw [Ink.Field.table_apply, Ink.Field.table_apply]; refine Finset.sum_congr rfl fun z _=>?_ ; unfold Ink.Field.site; have h' i (hx:i ∉ Set.range F): G.fee i* invoice z (G.slip i) x=0:= by rw [show G.fee i=_ from (hg i hx).1,zero_mul]
 let l i:=Q.fee i* invoice z (Q.slip i) x
 rw [← (F.injective.tsum_eq (f:=fun i=> G.fee i* Ink.invoice z (G.slip i) x) ?_)]; swap
 · exact by intro i hi; by_contra H; exact hi (h' _ H)
 rw [← tsum_subtype_eq_of_support_subset (f:=l) (s:=X) (hs:= by intro i hi; by_contra he; exact hi (mul_eq_zero.mpr (.inl (not_not.mp he))))]
 refine tsum_congr (fun i=> congr_arg₂ (·*·) (he i) (congr_arg (fun j=> Ink.invoice z j x) (hf i)))
end Tune
open Dais
-- Caller Art.Record at horizon N. specify frame query `Grade κ` Art. construct partially.
variable (T:Tune ((Coarse G)⊕α)) (s:Senses R)(Z:Zora.Noon G N)(o:α→Site n) {k₁ r:ℕ}
    (p:Lattice.Order)(v:ℕ)
set_option quotPrecheck false
local notation "w"=> T.slip v
local notation "d"=> List.length (Dais.coin (T.slip v))
local notation "V"=> T.fee v
variable {j:ℕ} (hq:k ≤ N) (h:T.typeR.Good a b k)
lemma silent : (Vase.vac s G r).sizeC=0:= by unfold Vase.vac Vase.sizeC; simp
lemma blind (z:Site n): (Vase.vac s G r).read z k=fun _ => 0:= by ext1 x; rw [Vase.globe]; simp [Vase.vac]
-- cost before stamping
include h hq
private lemma viable (hj: Dais.good s.val (chain w)) : (List.length (Dais.coin (T.slip v))) ≤N:= (Dais.enough hj (h.length v)).trans ((Nat.sub_le ..).trans hq)
noncomputable def how (r:ℕ)(v:ℕ): Vase s G r:= if H: Dais.good s.val (Dais.chain (T.slip v)) ∧ r=List.length (Dais.coin (T.slip v)) then H.2.symm ▸ Dais.crust p H.1 Z (viable T s v hq h H.1) (T.fee v) else Vase.vac s G r -- needs explicit viability
local notation "P"=> how T s Z p hq h
local notation "F"=> Dais.coin (T.slip v)
lemma issued (hp: Dais.good s.val (Dais.chain (T.slip v))): (P (List.length (Dais.coin (T.slip v))) v)= Dais.crust p hp Z (viable T s v hq h hp) V := by
 unfold how; rw [dif_pos ⟨hp,rfl⟩]
lemma level (hp:Dais.good s.val (Dais.chain (T.slip v)) ∧ r=d): (P r v).stage= hold hp.1:= by obtain ⟨h0,rfl⟩:= hp; rw [issued T s Z p v hq h h0]; rfl -- explicit params order look
lemma vacuum (hp:¬(Dais.good s.val (Dais.chain (T.slip v)) ∧ r = d)): P r v= Vase.vac s G r:=dif_neg hp
variable {u:ℝ} (ht:0<u)(hx:u * (5*k:ℝ)≤ a)
abbrev postage (k r:ℕ)(u:ℝ):= Zora.Noon.bill G Z r * Real.exp (u*(2*k:ℝ))
local notation "C"=> postage Z k r u
include ht hx
lemma paid_step : (P r v).fare u ≤ postage Z k r u * T.typeR.price a v:= by
 by_cases hv:Dais.good s.val (Dais.chain (T.slip v))∧ r=d; swap; · rw [vacuum _ _ _ _ _ hq h hv, Vase.fare,silent,zero_mul]; exact mul_nonneg (mul_nonneg (bill_pos ..) (Real.exp_pos _).le) (h.pay.1 v)
 rw [hv.2,issued T s Z p v hq h hv.1]; refine le_trans (buys p Z _ _ _ (h.length v) ht hx) (le_of_eq ?_); exact mul_assoc ..
lemma poem (r:ℕ) : Album.Health (how T s Z p hq h r) u (postage Z k r u*b):= by let A':= P r; let Z':= postage Z k r u; apply sumBudget_mono (b:=fun i:ℕ=>Z'*T.typeR.price a i) (sumBudget_mul_left h.pay (mul_nonneg (bill_pos ..) (Real.exp_pos _).le)); exact fun i=> mul_nonneg (Vase.nn_size ..) (Real.exp_pos _).le; exact fun i=> paid_step T s Z p i hq h ht hx; exact le_rfl
end Ballad
end YM.Qlocal.Quipu.Eluder
