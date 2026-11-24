import YM.AllOrder.Catch.Prism
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {ι:Type*} {T:Clock ι} {X Y:ι→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)][∀ i,Fintype (Y i)][∀ i,DecidableEq (Y i)]
variable (V:∀ i:ι,ℝ×(X i × Body (Y i))→ℝ) (W:∀i,X i)
    {A B:∀i,X i× Body (Y i)→ℝ}{M:∀i,X i→ Matrix (Y i) (Y i) ℝ}{ρ:∀ i,X i→Body (Y i)}
-- Morph to EVERY Y filter allowed. require growth Flow for given tableau.N.Incr order exact same Hess (paid.Octane). Need n+3 derivatives on Venue + Lift.Enough requested. Choose Holder proof rewriting.N=H+3. Good.
variable (D u v b p:ι→ℝ) {s z₁:ℝ}{k j:ℕ}
local notation "Ω" x=> X x × Body (Y x)
local notation "Γ"=> fun i=> grace (A i) (B i) (ρ i) (M i)
variable {W b V D u p} (U:Vaccine (k+3) D u p T A B ρ M)(N:North W b u T) (S:Flood V T (k+3))
local notation "F"=> fun i=> course (W i)
local notation "Pt"=> Clock.tier (fun i=>Body (Y i)) T
local notation "Ph"=> T.book (fun i=> closedBall (0:Body (Y i)) (D i))
variable {η:Type*}
local notation "H₀"=> T.Meter
local notation "N₀"=> (k+3)
local notation "ℍ"=> T.book (fun i:ι=>closedBall (0:ℝ) (b i))
include U
local notation "At"=> T.stage (fun i=> Body (Y i))
local notation "J"=> (Σ i:ι,Body (Y i))
local notation "L"=> (k+3)
local notation "tx"=> T.bookF
include N S
-- growth power proof
local notation "λ'"=> fun i v=> warmP (A i) (B i) (M i) (ρ i) (V i) (W i) v
lemma hearth (hj:j≤k): (Pt).Quite (fun i=> someJ (λ' i.1 i.2) j):=by
 let W₀:J→ℝ:=0; have h:Tendsto (Sigma.fst) (Pt).rail T.rail:=tendsto_comap; have he := h.eventually ((U.D_live.and S.rise).and U.pos)
 let η:= Pt; have ht:η.Meter (fun i=>‖i.2‖) 1:= Clock.windy T (fun i=> Body (Y i)); let X i:=X ((i:J).1); let f (i:J):= V i.1 -- x shadow
 let g (i:J)(t:ℝ):= (Γ) i.1 i.2 (t,F i.1 t); let ℓ (i:J)(t:ℝ):= uplift (F i.1) (ρ i.1) i.2 t; let M' (i:J):= plunge (V i.1) (W i.1) i.2 (ρ:=ρ i.1)
 have hw:η.Meter (fun i=>‖W i.1‖) 0:= Clock.grow (N.W_age.pays Sigma.fst (T.liftF _)) _ le_rfl; have hz i:‖(W₀ i)‖=(0:ℝ):=norm_zero; have hr:Cover (V:=fun _=>ℝ) (U:=X) η (L) 0 (fun _=>1) (fun (i:J)=> F i.1) W₀:= (Catch.ray _ (le_refl 0) ((Meter.const _ _)) hw).weak (by simp); let hI:= (show Cover (V:=fun _=>ℝ) (U:=fun _=>ℝ) η (L) 0 (fun _=>1) (fun _=> id) W₀ from Cover.exponent (C:=0) le_rfl (Meter.const η ‖(0:ℝ)‖)); let D' (i:J):= D i.1*(1+‖i.2‖)
 have hp:η.Meter (fun i=>p i.1) 0:= Clock.grow (U.price.pays Sigma.fst (T.liftF _)) _ le_rfl; have hh:η.Meter D' 1:= Clock.Meter.unitPay (a:=0) (f:=fun i:J=> D i.1) (Clock.grow (U.rate.width.pays Sigma.fst (T.liftF _)) _ le_rfl) le_rfl (((Meter.const η _).weak zero_le_one).add ht)
 have hx:Cover (V:=X) (U:=fun i=>Body (Y i.1)) η (L) 0 (fun _=>1) (fun i=>ρ i.1) (fun i=> F i.1 (W₀ i)):= Cover.has hp (he.mono fun i hi=>((hi.1.1.1.curve _ (by simp [course,W₀,hi.1.1.1.pos])).smaller (by omega)))
 have hζ:η.Quite (fun i=> someJ (g i) j):= by
     obtain ⟨s,hs⟩:=chumQ (T:=η) ⟨_,hp⟩ (D:=D') ⟨_,hh⟩ (L) -- syntax
     let H i t:=(t,F ((i:J).1) t); refine ⟨_, cover_j (Cover.comp le_rfl (hI.join hr) (u:=fun i=> (Γ) i.1 i.2) (Cover.has hs ?_)) (by omega : j ≤ k+3) ⟩; filter_upwards [he] with i hi; let E:= hi.1.1.1; let q:= E; let D'' := D' i; let z:= (1+‖i.2‖); have hW := Vote.golf_high E (c:=z) (le_add_of_nonneg_right (norm_nonneg _)); have hv : ‖i.2‖≤D' i:= (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_left (by positivity) hi.2); have hx : H i (W₀ i)=(0,0):= by simp [H,W₀,course]
     change Brush (L) _ _ _ (H i (W₀ i)); exact hx.symm ▸ (show Brush (L) (Lantern.fee (L) (p i.1) D'') 1 (Γ i.1 i.2) (0,0) from Lantern.compel (D' i) hW (norm_zero.trans_lt hW.pos) (norm_zero.trans_lt hW.pos') hv)
 have hw':Cover (V:=fun _=>ℝ) (U:=fun i=> Body (Y i.1)) η (L) 0 (fun _=>1) (fun i=>ρ i.1 ∘ course (W i.1)) W₀:= (Cover.comp le_rfl hr hx).weak (by simp)
 have hm:Cover (V:=fun _=>ℝ) (U:=fun i=>ℝ×(X i × Body (Y i.1))) η (L) 2 (fun _=>1) ℓ W₀:= by
     have ha:0 ≤ (2:ℝ):=(by norm_num); let hA:=(Catch.ray (k:=k+3) (ι:=J) (X:=fun i=>Body (Y i.1)) (fun i=>i.2) zero_le_one ((Meter.const η (0:ℝ)).weak zero_le_one) ht); exact (hI.weak ha).join ((hr.weak ha).join ((hw'.weak ha).add (hA.weak (by norm_num : (1:ℝ)+1 ≤ 2))))
 have hC:Cover (V:=fun _=>ℝ) (U:=fun _=>ℝ) η (L) (1+2*(k+3:ℕ)) (fun _=>1) (fun i=> V i.1 ∘ ℓ i) W₀:= by
    let V₁ (i:J):= ℓ i (W₀ i); let u:= fun (i:J)=> T.cost i.1^(1:ℝ); have hu:η.Meter u 1:= Clock.grow ((Meter.pale T 1).pays Sigma.fst (T.liftF _)) _ zero_le_one
    refine Cover.comp (u:=f) (b:=1) (by norm_num) hm (Cover.has hu ?_); filter_upwards [he,h.eventually (S.ticket 1 zero_lt_one)] with i hi hB; exact hB (V₁ i) (by rw [show V₁ i=0 by simp [V₁,ℓ,W₀,uplift,course, hi.1.1.2.steer.map0]]; simp)
 have hM:η.Quite (fun i=> someJ (M' i) (j+2)):= Exists.intro _ (cover_j hC (by omega : j+2 ≤ k+3)); apply (hζ.add (Quite.neg hM)).monotone; filter_upwards [he] with i hi; obtain ⟨⟨⟨hX,hH⟩,hS⟩,hx⟩:=hi; let h:= sign _ (W i.1) hH hS i.2; change |someJ (g i-climb2 (M' i)) j|≤_; rw [some_sub («F»:=g i) (worth (W:=W i.1) hH hS i.2) (shifty (shifty h.2.2.2)),retrace («h»:=M' i) h.1 h.2.1 h.2.2.2,Pi.sub_apply,sub_eq_add_neg]
-- j=0 heater.Enroll `run` jets via warmth at β. Do not project Rank of ratePlan directly on marks.
lemma surge (hj:j≤k): (Pt).Quite (fun i=> someJ (Real.exp ∘ λ' i.1 i.2) j):= by
 choose C hC using fun l (hl:l≤k)=> hearth U N S hl; let t' (p:Fin (k+1)):= C p.val (by have h:=p.isLt; omega); let t:= ∑ i:Fin (k+1),|t' i|; have ht:0≤t:=sum_nonneg fun _ _=> abs_nonneg _
 let V' i:=λ' (i:J).1 i.2; let A' i:= someJ (V' i); have hp:= (show Tendsto Sigma.fst (Pt).rail T.rail from tendsto_comap); let he:= hp.eventually (U.D_live.and S.rise);
 have hh: Cover (V:=fun _=>ℝ) (U:=fun _=>ℝ) (Pt) j t (fun _=>1) (fun i=>delay (A' i) j) 0:= by
    apply (TaylorCap.delaying (v:=0) (k:=j) (s:=t) (f:=A') ?_ (Meter.const _ 0) le_rfl).weak; -- apply... goal order
    · simp
    intro l hl; let i:Fin (k+1):=⟨l,(by omega)⟩; exact (hC l (hl.trans hj)).weak ((le_abs_self _).trans (single_le_sum (f:=fun i:Fin (k+1)=>|t' i|) (fun _ _=> abs_nonneg _) (mem_univ i)))
 have hz : Tendsto (fun i=>delay (A' i) j 0) (Pt).rail (𝓝 0):= tendsto_const_nhds.congr' (he.mono fun i hi=> by dsimp only; rw [delay_zero]; unfold A'; rw [someJ_zero]; exact (initial hi.1.2 hi.2 i.2 (W:=W i.1)).symm)
 have hw := cover_j (h:= (Cover.comp ht hh (u:=fun _=> Real.exp) (Cover.loc Real.contDiff_exp.contDiffAt hz))) (le_refl j); refine ⟨_, hw.eq_mem (he.mono fun i hi=>?_ )⟩; exact (congr_fun (Laplace.SigmaP.conviction (fee hi.1.2 hi.2 (i.2) (W:=W i.1))) j).symm
end YM.AllOrder.Catch
