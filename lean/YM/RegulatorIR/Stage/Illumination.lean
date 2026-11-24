import YM.RegulatorIR.Stage.Film

/-! W1 and moment readiness exported for true clock input.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Stage
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X:Type} {M:X→ℕ} {n:Page M→Side} (S:Circuit M n){K:KernelChoices}(Y:Program K) (G:Gauge)(Z:∀ P:Patch,P.Branches K G)(t:Page M→Scale)
local notation "A₁"=> S.dialect Y G Z t
local notation "T₁"=> S.lane Y G Z t
local notation "Q₁"=> S.payroll Y G Z t
variable (k:ℕ) (f:Flap M)
lemma kernel_b (k): ∀ p:Page M,∀ i j, Knows ((A₁).census.cone k p) ((Q₁).bulk p i j):= Page.proves (fun w p r=> learns_m S Y G Z t w p r k) (fun i=> traveling _ _ _ _ _ i k) -- parameters
lemma symmetricV : ∀ p:Page M,gradedSymmetric ((Q₁).bulk p):=by
 refine Page.proves ?_ ?_
 · intro i; let v:=Page.opening M i;have hp:= Circuit.serene G t i; exact (Prim.ark (t v) (S.dual v) (S.comet v) hp).symm
 intro i _ p j;rw [← (Q₁).step_v]; unfold GridStep.pure;split;exact symmetric_zero;exact crop_symm _ _ (Packet.is_symmetry _) -- inference
lemma extentV (w:Page M) (i j:ℕ) : Throughout ((Q₁).bulk w i j):=by
 intro p x; exact Passage.cells (R:=T₁) (fun _=>rfl) (S.follows Y G Z t) (S.passage Y G Z t) w p i j x

lemma moment0 (α:Page M) : Throughout (coil ((T₁).stem α)) := by
 intro x y; let p:= linksQ G
 have h:= crustA G (S.tables Y α) (y 0) (y 1) x
 rw [site_roll, site_roll] at h
 exact congr_arg ((-1/2:ℝ) * ·) h

-- Unit page transport. comfortable Film.Pin.V.B.
private lemma unitPoly {X:Type}[Finite X](L:Meter X)(f:X→ℝ≥0∞)(h:∀ x,f x≠⊤): Poly L f:=by
 letI : Fintype X:= Fintype.ofFinite X
 refine ⟨∑ x,f x, 0,ENNReal.sum_ne_top.mpr (fun _ _=>h _),fun w=>?_⟩; rw [pow_zero,mul_one]; exact Finset.single_le_sum (f:=f) (fun _ _=>zero_le) (mem_univ w)

lemma illumination (p:Page M)(e:ℕ): W1 (dyeX ((T₁).stem p) ((Q₁).bulk p)) e:=by
 let w:X:= p.bindW; let f:=fun _:Unit=>w; let g:=Centered.album (A₁) f; let H:=Profiles.sails (T₁) f; let V:= Centered.movie (Q₁) f;let P:= stages f M;let a:= arrow f M; let N:=g.census; let F: Page (M ∘ f) := ⟨(),p.downW,p.good⟩; let k:=14; let ht:= S.follows Y G Z t
 have hp : H.Follows V:=fun i=> ht w
 have hc : Common H:=fun i=>rfl
 have he:P F=p:=by cases p; rfl
 obtain ⟨hs,_,hB⟩:= con S Y G Z t p
 rw [← he] at hs hB; rw [← he];
 letI : Finite (Page (M ∘ f)):= Finite.of_injective (fun i:Page (M ∘ f)=> (⟨i.downW,Nat.lt_succ_of_le i.good⟩: Fin (M w+1))) (fun i j h=>by rcases i with ⟨i,x,hp⟩;rcases j with ⟨j,v,ht⟩; have hx:x=v:=congr_arg Fin.val h; rcases i;rcases j;subst x;rfl)
 letI : Finite (Flap (M ∘ f)):= Finite.of_injective (fun i:Flap (M ∘ f)=> (⟨i.offset,i.ok⟩: Fin (M w))) (fun i j h=>by rcases i with ⟨i,x,hp⟩;rcases j with ⟨j,v,ht⟩; have hx:x=v:=congr_arg Fin.val h; rcases i;rcases j;subst x;rfl)
 have hu : g.Supplies V l₀ e k:=by
    refine ⟨fun i hi j=>?_,fun w i j he=> Halo.helium H V hp w i j⟩
    choose c hc H using fun w:Page (M ∘ f)=> kernel_b S Y G Z t k (P w) i j
    exact ⟨c,unitPoly _ c hc,H⟩
 have hK: Halo.Aug.Amenities g l₀ e k:=by
    let YQ:= Epoch.League.haloS S k G Y∘ a; let D w:= Epoch.League.paceS S k G Y (a w)+1; let hl:= flapL (M∘ f) l₀
    refine ⟨⟨YQ,unitPoly hl _ (fun w=>arc_p S Y G (a w) k),fun w=> physical S Y G Z t (a w) k⟩,⟨D,unitPoly hl _ (fun w=> ENNReal.add_ne_top.mpr ⟨panes_p S Y G (a w) k,ENNReal.one_ne_top⟩),fun w=> clockpost S Y G Z t (a w) k⟩,?_⟩
    intro i hi j
    refine ⟨_,unitPoly hl (fun w=> valor (t (a w).prev) i*Oracle.archive (S.pactP (a w)) K G (Z _) i j k) (fun w=> ENNReal.mul_ne_top (valor_f _ _) (archived _ _ _ _ _ _ _)),fun w=> startupK S Y G Z t (a w) i j k⟩
 exact Axial.enabled H V hp hc hu hK F (by omega) hs hB

-- actual T rank2 and all positive moments
variable (hG:G.Simple) (w:Page M)
local notation "T"=> S.lane Y G Z t
include hG
lemma ort_K : Rules (coil ((T₁).stem w)):=by
 let H:= illumination S Y G Z t w 0; have hx: dyeX ((T).stem w) ((Q₁).bulk w) 0 2=coil ((T).stem w):=dif_pos ⟨rfl,rfl⟩
 let s:= (symmetricV S Y G Z t w);rw [← hx]
 apply allrules H le_rfl hG (hx.symm ▸ coil_s _ (con S Y G Z t w).2.1) (hx.symm ▸ moment0 S Y G Z t w)
lemma ort_T (e:ℕ)(h:0<e): Rules ((Q₁).bulk w e 2):=by
 let H:= illumination S Y G Z t w e; have hx: dyeX ((T).stem w) ((Q₁).bulk w) e 2= ((Q₁).bulk w) e 2:=by rw [dyeX,dif_neg];rfl;omega
 rw [← show _= (Q₁).bulk w e 2 from hx]; apply allrules H le_rfl hG (hx.symm ▸ symmetricV S Y G Z t w e 2) (hx.symm ▸ extentV S Y G Z t w e 2)
end YM.RegulatorIR.Stage
