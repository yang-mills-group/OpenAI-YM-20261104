import YM.OPE.Compatible.Signals.Pico
/-!
# Full costs on authenticated addresses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson Cells Extraction Word Spec OPE.Allot
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Final C F S)
variable {P: Prescription U.sector.derivatives}(hP:P.Coherent)
local notation "L'"=> U.sector.derivatives
variable {V B J:Type}[PartialOrder V][OrderBot V][Fintype V]{ψ: Filter B}{T:B→ℝ}
variable (A:Allot C)(D:Origin V){Q:Finset V}(p:brim D Q → C.book.Token)
variable {n d b:ℕ}{s:B→V→ℝ}{η M c:ℝ}
variable (hΓ:Glowing D Q ψ T s η) (hL:Lanes (F:=F) U.sector.derivatives)(h:Services C F S)(hp:1 ≤ b)(hM:0 ≤ M)
set_option quotPrecheck false
local notation "Ω"=> fun i=> volume D Q (fun a=> (p a).1) (s i)
local notation "R"=> fun i=> s i ⊥
include hΓ in
lemma Glowing.brim_paid :∀ᶠ i in ψ, 0< Ω i :=by
   filter_upwards [eventually_all.mpr (fun i:brim D Q => (hΓ.fade _ ((on_brim ..).mp i.2 |>.2.2)).eventually self_mem_nhdsWithin)] with i hi; exact Finset.prod_pos (fun x _=> pow_pos (hi x) _)
local notation "K"=> fun i=> schedule C b η (s i) ⊥-1
local notation "adr"=> fun v i (z:V→E4)=> Address C D Q v b (T i) (s i) η M z
include A hΓ hP h hM hL hp
lemma pol_coeff (v:ℕ)(a:Mode L') : ∃ f:B→ℝ,Score ψ T f ∧ ∀ᶠ i in ψ, ∀ z,Address C D Q v b (T i) (s i) η M z → ‖P.ope a (picked (brim D Q) z) p 0‖ * Ω i/R i^a.fst ≤ f i:=by
   let d:=a.fst
   obtain ⟨g,b',u,hg,hb,hu,k,hk⟩:= simultaneously U P A D p (sole (C.book.one 0)) hΓ hL.toInward h.simpleGate h.schedule hp hM v d (c:=1) zero_lt_one
   obtain ⟨L,hB⟩:= mode_top U P hL.toOutward hP d; obtain ⟨_,he,hr,-⟩:= prev_info D h.simpleGate A hΓ b
   let y i:=β C (K i)^L; have hS := hg.sum ((hr.power L hΓ.ray).mul hu) hΓ.ray; refine ⟨_,hS.up,?_⟩; filter_upwards [hk,he.eventually hB,hΓ.brim_paid D p,(hΓ.fade _ hΓ.crowned.base).eventually self_mem_nhdsWithin] with i hi hx hΩ hh z hz
   obtain ⟨W,x,p',q,hq,hU,_⟩:=hi z hz; have hb:= hx a rfl hq; let c:= P.test a d (S.project _ q); let w:= P.ope a (picked (brim D Q) z) p 0; have ha : ‖w‖ ≤ g i + y i*u i:= (le_of_eq (congr_arg norm ((sub_add_cancel w c).symm))).trans ((norm_add_le ..).trans (add_le_add (hU _ ((full_bands ..).mpr le_rfl)) hb)); change ‖w‖ * Ω i/R i^d≤ _; refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hΩ.le) (pow_nonneg (le_of_lt hh) d)).trans_eq ?_; ring
variable [Fintype J] (w:J→ C.book.Token)
lemma pol_error (v d:ℕ) (hc:0<c) : ∃ f:B→ℝ, Score ψ T f ∧ ∀ᶠ i in ψ,∀ z,Address C D Q v b (T i) (s i) η M z → ∀ y:J→E4, ClearOf 0 y c → ∀ r:Viewers U, ‖observe (spectator U r) (beside (picked (brim D Q) z) y) (beside p w)- P.truncated (spectator U r) d (picked (brim D Q) z) p 0 y w‖*Ω i/R i^(d+1) ≤ f i:=by
   obtain ⟨g,b',u,hg,hb,hu,k,hk⟩:= simultaneously U P A D p w hΓ hL.toInward h.simpleGate h.schedule hp hM v (d+1) hc
   obtain ⟨L,hB⟩:= mode_top U P hL.toOutward hP (d+1); obtain ⟨_,he,hr,-⟩:= prev_info D h.simpleGate A hΓ b; obtain ⟨A,hA,hZ⟩:= page_total U P w (d+1) h.schedule hc; let n:ℝ := ↑(bands L' (d+1)\bands L' d).card; let m:ℝ := ↑(bands L' d).card
   let X i:=β C (K i)^L; let Y i:=g i*Ω i/R i^(d+1); let Z i:=u i*Ω i/R i^(d+1); let W i:=Y i + (n*(X i*Z i*A)+m*(Y i*A)); have hW:Score ψ T W:= hg.up.plus ((((Score.steady n hΓ.ray).product (((hr.power L hΓ.ray).up.product hu.up).product (Score.steady A hΓ.ray))).plus ((Score.steady m hΓ.ray).product (hg.up.product (Score.steady A hΓ.ray))) hΓ.ray)) hΓ.ray
   refine ⟨W,hW,?_⟩; filter_upwards [hk,he.eventually hB,hΓ.brim_paid D p,(hΓ.fade _ hΓ.crowned.base).eventually self_mem_nhdsWithin,close_of_tend D hΓ.crowned (η:=η) (M:=M) (hΓ.fade _ hΓ.crowned.base) hc] with i hi hK hp hs hh z hX y hy r; obtain ⟨e,x,p',q,hq,hg,hY⟩:= hi z hX; let S':= spectator U r
   let v:= picked (brim D Q) z; have hv:= hy.inject_both hc; have hV: Injective (beside v y):= beside_distinct.mpr ⟨hX.screen.coin,(beside_distinct.mp hv).2.1, fun j m hk'=>by
       have hx:= hh z hX.ridge j; change ‖v j‖ < _ at hx; rw [hk'] at hx; have hh:=hy.openSpace m; rw [zero_sub,norm_neg] at hh; linarith⟩
   let A' := observe S' (beside v y) (beside p w); let B:= P.truncated S' d v p 0 y w; let Q:= observe S' (beside (sole (0:E4)) y) (beside (sole (⟨d+1,q⟩ : C.book.Token)) w); have hQ:‖A'-B‖ ≤ g i + (n*(X i*u i*A)+m*(g i*A)):=by
       calc
          _ = ‖(A'-Q)+(Q-B)‖:=by rw [sub_add_sub_cancel]
          _ ≤ _ := (norm_add_le ..).trans (add_le_add (hY y hy hV r) (less_trunc U P w hP r q hv (fun a ha=> hg a ((full_bands ..).2 (((full_bands ..).1 ha).trans (Nat.le_succ _)))) (fun a h=> hK a h hq) hA (hZ y hy r)))
   change ‖A'-B‖* _ /_ ≤ _; refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQ hp.le) (pow_nonneg (le_of_lt hs) _)).trans_eq ?_
   unfold W Y Z; ring
end YM.OPE.Arboreal
