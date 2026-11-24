import YM.RG12.Kintsugi.Outlet
import YM.RG12.Alidade.Rental
import YM.RG12.Alidade.Fades
/-! # Horizon-*arbitrary* physical outlet: expectation sector

Here even signed scalar operators are allowed. Use actual position probes at
one-point arity with *full* transported columns, no detector of whole physical
S.Field (or inverse cost). Combine with the saved margin for all w< next positive
grade tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi.Spot
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Arche
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East Commission
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff)
variable {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hp:Scrim C W u ψ β δ (fly C.path.levels) r L)(he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤f.fuse)(hG:G.Simple)
local notation "χ"=>C.path.levels.clock.hatBeta
local notation "A!"=>C.path.levels
set_option quotPrecheck false
local notation "ℱ"=> (Ultrafilter.of ϕ:Filter _)
lemma at_one {L:Register G} (T : Table L) (d:ℕ)(v:T.Field d): expectation T d v=T.useAt T 0 (fun _:Fin 1 => (⟨d,v⟩:T.Tag)):=by
   rw [expectation,Work.A01.front_eval]; congr 1; funext i; rw [@Subsingleton.elim (Fin 1) _ i 0,Fin.cons_zero]
include h hp he hf hG
lemma pence (d:ℕ) (x:C.label d):
    let i:Fin (d+1):=Fin.last d
    let t:=(P.panels d 0).arc; let n:=trays d
    ∃ c:ℝ,0≤ c∧∀ᶠ k in atTop,∀ T:ℕ→ℕ→TableL C d,Poised (P.panels d) P.chart U.room.cutoff P.haar P.locality n (P.budget d) k T→
     ∀ Z:TableL C d,Comparer (ϕ:=ϕ) (hC:=U.room.cutoff) (ℱ) k d T (mag (A!) t k) Z → ‖expectation S _ (glowH M k (Z i) x)-expectation (Cells.standard C) d ((Cells.standard C).project d x)‖ ≤ c * Ship.budget (A!) n k:=by
   intro i t n; let a:=fun _:Fin 1=>i; let b:Fin 1 → Lattice.Cover:=0; let y:(j:Fin 1)→C.label (a j):=fun _=>x
   have h₁ : (0:Points (0+1))∈conf 1:=Next.UVStress.conf1
   have hn:2≤n:= by dsimp [n, MergeProof.East.trays]; omega -- trays defeq
   obtain ⟨c,hc,hE⟩:= literal (P.panels d) P.chart U.room.cutoff hG hp P.haar P.locality _ (h.covered.2.1 d) 0 a y (R:={0}) isCompact_singleton (Set.singleton_subset_iff.mpr h₁) hn (by omega) f (Maxwell.table_smooth _)
   refine ⟨c,hc,?_⟩
   filter_upwards [hE] with k hk T hT Z hZ
   let μ:=mag (A!) t k
   have hv {x:Points 1}:x∈generic _:=fun _ _ _ _=>Subsingleton.elim ..
   have ht(x:ℝ) :tag x b=0:=by ext1 i; ext1 j; change x * (↑(0:ℤ):ℝ)=(0:ℝ); simp
   have hg : Order.grid C k b=0:= by ext1 i; ext1 j; change C.S.a k * (↑(0:ℤ):ℝ) = (0:ℝ); simp
   have hx:=hk T hT b (Set.mem_singleton_iff.mpr (ht _)) hv
   let K(p:UVIndex) := ladd C μ k p.1 p.2 i (T p.1 p.2 i); let e:=aligned C M k (Z i)
   let Y := fun _:Fin 1=>e x; let V(p:UVIndex):=fun _:Fin 1=>K p x
   let c':Caps 1:= fun _=>d
   have hC:= OPE.Cards.variation (k:=k) (d:=c') b U.room.generic hv Y V (fun _=>tends_aligned he hZ i x (hT.early _ (le_refl _))) (hZ.filter_le.trans hf)
   let F:=(Cells.standard C)
   have hl:=fun (hi : S.Symmetric)=> S.at_project S hi (fun _=>le_rfl) h₁ (fun _:Fin 1=> (⟨d,e x⟩:C.book.Token))
   have ha: S.value c' (Order.grid C k b) Y= expectation S _ (glowH M k (Z i) x):=by rw [hg,at_one];exact (hl U.room.kernel.laws.toSymmetric).symm
   have hq:= (hC.sub_const (expectation F _ (F.project d x))).norm; rw [ha] at hq
   apply le_of_tendsto hq
   let z(p:UVIndex):=((C.ensemble c' (fun i=>location C.S k p.1 p.2 (b i))) (V p))
   have hy:∀ᶠ p in f.fuse, ‖z p - disc (jointX y) (tag (Station.mag (A!) t k)⁻¹ b)‖ ≤ c*Ship.budget (A!) n k:=hx
   have hN:disc (jointX y) (tag (Station.mag (A!) t k)⁻¹ b)=expectation F _ (F.project d x):=by rw [ht,at_one]; rfl
   rw [hN] at hy; exact hy.filter_mono (hZ.filter_le.trans hf)

def nectar (d:ℕ)(k:ℕ)(A:Module.End ℂ (C.label d)): C.label d→ₗ[ℂ]ℂ:= (expectation S d).comp (glowH M k A)
lemma bouquet (d:ℕ):
    let i:Fin (d+1):=Fin.last d
    let t:=(P.panels d 0).arc; let n:=trays d
    ∃ c:ℝ,0≤ c∧∀ᶠ k in atTop,∀ T:ℕ→ℕ→TableL C d,Poised (P.panels d) P.chart U.room.cutoff P.haar P.locality n (P.budget d) k T→
     ∀ Z:TableL C d,Comparer (ϕ:=ϕ) (hC:=U.room.cutoff) (ℱ) k d T (mag (A!) t k) Z → ∀ x:C.label d, ‖nectar (S:=S) M d k (Z i) x- expectation (Cells.standard C) d ((Cells.standard C).project d x)‖ ≤ c * Ship.budget (A!) n k * mass C d x:=by
   intro i t n
   let I:=Fin ((C.labels.level d).extra+1)
   let e(x:I):C.label d:=Pi.single x 1
   choose B hB HB using fun x=>pence U M P h hp he hf hG d (e x)
   let A:= ∑ x:I, B x; refine ⟨A,sum_nonneg fun i _=> hB _,?_⟩
   filter_upwards [eventually_all.mpr HB] with k hk T hT Z hZ x
   have hY(r:I) : B r ≤ A:= single_le_sum (fun s _=>hB s) (mem_univ _)
   let J := nectar (S:=S) M d k (Z i) - (show C.label d→ₗ[ℂ] ℂ from (expectation (Cells.standard C) d).comp ((Cells.standard C).project d))
   change ‖J x‖≤_
   have hx : x=∑ j:I,x j • e j:=by
      funext j; simp [e,Finset.sum_apply,Pi.single_apply,mul_ite]; exact (sum_ite_eq _ j _).trans (if_pos (Finset.mem_univ j)) |>.symm
   conv_lhs=> rw [hx]; rw [map_sum]
   simp_rw [map_smul]
   refine (norm_sum_le ..).trans ?_
   unfold mass Labels.Frame.coeffSize; rw [mul_sum]
   refine sum_le_sum (fun j _=> (le_of_eq (norm_smul ..)).trans ?_)
   have hy:= (hk j T hT Z hZ).trans (mul_le_mul_of_nonneg_right (hY j) (Ship.budget_pos ..).le)
   exact (mul_le_mul_of_nonneg_left (show ‖J (e j)‖≤_ from hy) (norm_nonneg _)).trans_eq (mul_comm ..)
lemma good_mean (d:ℕ):∀ᶠ k in atTop, lit k → Quoter M (expectation S d) 1 0 k:=by
   let K:=Cells.standard C
   let n:=MergeProof.East.trays d
   let A : C.label d→L[ℂ] ℂ:= LinearMap.toContinuousLinearMap (show C.label d→ₗ[ℂ] ℂ from (expectation K d).comp (K.project d))
   obtain ⟨B,hB,hY⟩:=bouquet U M P h hp he hf hG d
   have hn:1 ≤ n:= by unfold n MergeProof.East.trays; omega
   let q:=(P.panels d 0).arc; have hq:0 ≤ q:=by unfold q; linarith only [(P.panels d 0).huge,Nat.cast_nonneg (α:=ℝ) d]
   let J:= (B+‖A‖)*(2^d*(3/2:ℝ))
   filter_upwards [hY,(Ship.diminishes (A!) n hG hn).eventually (ge_mem_nhds zero_lt_one),h.offers d,(hat_grows (C:=C) hG).eventually_ge_atTop J] with k hk hc ha ht hL
   obtain ⟨L,hv⟩:= ha hL
   let b:=mag (A!) q k
   obtain ⟨Z,hZ⟩:= compare_in he hv.early hv.charts b (by dsimp [b]; rw [mag_bill]; exact Glimmer.costed q _ hq) (Ultrafilter.of ϕ) (Ultrafilter.of_le ϕ)
   let i:Fin (d+1):=Fin.last d
   intro v; obtain ⟨z,rfl⟩:=(produced hZ i).2 (show C.label i from v)
   let D:=C.S.a k; have hD:0<D^d:=pow_pos (C.S.a_pos k) d
   have hr: nectar (S:=S) M d k (Z i) z = (↑(D^d):ℂ) * (expectation S d) (S.project d (M d k (Z i z))):= by -- scalar map
      dsimp only [nectar,glowH,Arche.aligned,LinearMap.smul_apply,LinearMap.comp_apply]; rw [map_smul,map_smul]; rfl
   have heq := (norm_sub_norm_le (nectar (S:=S) M d k (Z i) z) (A z)).trans (hk L hv Z hZ z)
   have hx:= (A.le_opNorm z).trans (mul_le_mul_of_nonneg_left (norm_le_mass ..) (ContinuousLinearMap.opNorm_nonneg ..))
   let t:=mass C d z
   rw [hr,norm_mul,Complex.norm_real,Real.norm_of_nonneg hD.le] at heq
   have hz: 0 ≤ t:=mass_nonneg ..
   have hM : 0 ≤ B+‖A‖:=add_nonneg hB (ContinuousLinearMap.opNorm_nonneg ..)
   have hI:=mul_le_mul_of_nonneg_left hc hB
   have hh: D^d*‖expectation S d (S.project d (M d k (Z i z)))‖ ≤ (B+‖A‖)*t:=by
      change _ - _ ≤ B * Ship.budget (A!) n k * t at heq
      change ‖A z‖ ≤ ‖A‖ * t at hx
      nlinarith only [heq,hx,mul_le_mul_of_nonneg_right hI hz]
   have hv:=hh.trans (mul_le_mul_of_nonneg_left (hZ.base i z) hM)
   rw [pow_one,Nat.sub_zero,div_mul_eq_mul_div,le_div_iff₀ hD]
   rw [← mul_assoc] at hv; rw [mul_comm _ (C.S.a k ^ d)]; exact hv.trans (mul_le_mul_of_nonneg_right ht (mass_nonneg ..))
-- no scrim assumptions not in facilities
omit hp in
lemma sold_mean (Q:OPE.Facilities C f S) (d:ℕ):∀ᶠ k in atTop,Quoter M (expectation S d) (d+2) 0 k:=by
   obtain ⟨Q',r,L,hQ⟩:= Q.costlier
   exact the_price_out U M P h hG he _ (good_mean U M P h (hQ.toPackage.toTableTickets.system) he hf hG d)
omit h hp he hf in
lemma melted_out (hr:Rail.Slugg (A!))(hc:Alidade.Credible S U.sector.derivatives M){d w:ℕ}(hW:w<d)(L:S.Field d→ₗ[ℂ]ℂ)(hL:∀ e:ℕ,∀ ha:e<w+1,∀ x:S.Field e, L (U.sector.derivatives.rise (ha.le.trans (Nat.succ_le_of_lt hW)) x)=0) : ∀ᶠ k in atTop,Quoter M L 0 w k:=by
   obtain ⟨A,hA,he⟩:= hc.erase d (w+1) L (by omega) hL
   have ht:= (Alidade.waste (A!) hG (MergeProof.East.trays d) (by unfold MergeProof.East.trays; omega) hr).const_mul A
   rw [mul_zero] at ht
   have hR:= Real.log_pos (x:=(3:ℝ)) (by norm_num)
   filter_upwards [ht.eventually (ge_mem_nhds hR),he,eventually_gt_atTop (0:ℕ)] with k hk heq he v
   let Q:= Alidade.MeltScale C d k
   have hK:(0:ℝ)< (k:ℝ):= Nat.cast_pos.mpr he
   change A*(Q / (k:ℝ)) ≤ Real.log 3 at hk; rw [mul_div_assoc',div_le_iff₀ hK] at hk
   have hg:= Alidade.epoch_pace (A!) k -- i+2 inequality
   have hz: Real.log 3 * (k:ℝ) ≤ C.S.scale k:=by
      unfold Alidade.epoch at hg
      apply le_of_sub_nonneg; field_simp at hg;linarith only [hg]
   have hq: Real.exp (A * Q) ≤ (C.S.a k)⁻¹:= by
      unfold Schedule.scale at hz
      rw [← Real.exp_log (inv_pos.mpr (C.S.a_pos k))]; exact Real.exp_monotone (hk.trans hz)
   apply (heq v).trans (mul_le_mul_of_nonneg_right _ (mass_nonneg ..))
   rw [show d-w=(d-(w+1))+1 from by omega,pow_zero,pow_add,pow_one]
   apply (div_le_div_of_nonneg_right hq (pow_pos (C.S.a_pos _) _).le).trans_eq; field_simp
end YM.RG12.Kintsugi.Spot
namespace YM.RG12.Kintsugi.Spot
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Arche
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East Commission
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Alidade.Route P lit U.room.cutoff)
variable (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤f.fuse)(hG:G.Simple)(H:OPE.Facilities C f S)
local notation "χ"=>C.path.levels.clock.hatBeta
local notation "h!"=>U.phase.transport.injection
local notation "H!"=>U.room.kernel.laws
include hG
lemma unit_desc {d:ℕ}(hx:d<4)(v:S.Field d):∃ z:ℂ,v=z • S.unit d:=by
   obtain ⟨x,rfl⟩:= S.onto d v
   obtain ⟨z,h⟩:=unit_spans hG C d (C.ref d) hx x
   refine ⟨z,?_⟩; rw [h,map_smul];rfl
omit hG in
include U in
lemma absolute_unit (d:ℕ): expectation S d (S.unit d)=1:=by
   let t:Fin 0→C.book.Token:= Fin.elim0
   rw [expectation,Work.A01.front_eval,S.at_unit (H!) conf1,show blank S=S.classTokens ∘ t from Subsingleton.elim ..,S.at_project S (H!).toSymmetric (fun _=>le_rfl) (Points.tail_in conf1)]
   exact (H!).trivial ..
include h he hf H
lemma earned_low (d w:ℕ)(hw:w <4): RowPrice C S U.sector.derivatives M d w:=by
   by_cases hd:d<4
   · exact low_row_price hG he S _ (H!) h! d w hd
   obtain ⟨Q,hQ⟩:= OPE.Prescription.chosen U.room.kernel.laws.toSymmetric h!
   have hC:=Alidade.weiner U Q hQ P hG he hf H h
   intro L H' hL
   cases w with
   | zero =>
      let a :=L (S.unit d); let D:=L-a • expectation S d; have hZ :D (S.unit d)=0:=by
         change _ - a * _ = 0; rw [absolute_unit U d]; dsimp [a];rw [mul_one,sub_self]
      have heq:∀ e:ℕ,∀ ha:e<1,∀ x:S.Field e, D (U.sector.derivatives.rise (ha.le.trans (show 1 ≤ d by omega)) x)=0:=fun e hi x=>by
         obtain ⟨z,rfl⟩:= unit_desc (S:=S) hG (by omega) x
         rw [map_smul,U.sector.derivatives.fixs h! (H!),map_smul,hZ,smul_zero]
      have hW:=melted_out U M hG h.free.speed hC (w:=0) (by omega) D heq
      refine ⟨d+3,?_⟩
      filter_upwards [hW,sold_mean U M P h.free he hf hG H d,(hat_grows (C:=C) hG).eventually_ge_atTop (1+‖a‖)] with k hk hv hβ x
      let β:=χ k;have hβ':1 ≤ β:= (C.path.levels.fits.delayed k).le
      let i:=mass C d x/C.S.a k^d;let y:=S.project d (M d k x)
      have hi:0 ≤ i:= div_nonneg (mass_nonneg ..) (pow_nonneg (C.S.a_pos _).le _)
      have hY:D y+a*(expectation S d y)=L y:=sub_add_cancel _ _
      specialize hk x; specialize hv x
      change ‖L y‖ ≤ _;rw [← hY]
      apply (norm_add_le ..).trans; rw [norm_mul]
      rw [Nat.sub_zero];replace hk: ‖D y‖ ≤ i:= by simpa only [Quoter,pow_zero,Nat.sub_zero,one_div, inv_mul_eq_div] using! hk
      replace hv: ‖expectation S d y‖≤β^(d+2)*i:=by unfold i; rw [mul_div_assoc']; simpa only [Nat.sub_zero,div_mul_eq_mul_div] using! hv
      rw [show (χ k ^ (d+3))/(C.S.a k^d)*mass C d x=β^(d+2)*β*i from by unfold i β; rw [pow_succ]; ring]
      change 1 + ‖a‖ ≤ β at hβ
      have ht:1 ≤ β^(d+2):=one_le_pow₀ hβ'
      apply (add_le_add hk (mul_le_mul_of_nonneg_left hv (norm_nonneg a))).trans
      nlinarith only [mul_le_mul_of_nonneg_right hβ (mul_nonneg (zero_le_one.trans ht) hi),mul_le_mul_of_nonneg_right ht hi]
   | succ w=>
      have ht(e:ℕ)(he:e<w.succ+1)(x:S.Field e) : L (U.sector.derivatives.rise (he.le.trans (show w.succ+1 ≤ d by omega)) x)=0:=by
         obtain ⟨a,rfl⟩:=unit_desc (S:=S) hG (by omega) x
         have hp:= hL 0 (Nat.zero_lt_succ w) (S.unit 0); rw [U.sector.derivatives.fixs h! (H!)] at hp
         rw [map_smul,U.sector.derivatives.fixs h! (H!),map_smul,hp,smul_zero]
      exact ⟨0,melted_out U M hG h.free.speed hC (by omega) L ht⟩
end YM.RG12.Kintsugi.Spot
