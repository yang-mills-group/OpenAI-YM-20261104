import YM.Qlocal.Reckoner.Translation
/-! Scribe export with true actual fields, including extra markers fused or removed.
 Weight conditions before tests every label that is alive. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V I Ω J J' J₀ K α:Type}[DecidableEq V][DecidableEq I]{G:Gauge}{n:Side}{R:Census I}
variable {X: RG.Rep G n}{s:V→ Support n}{s':I→Support n} {A A' B B' u v a t w δ:ℝ} {o: V→Site n}{o':I→Site n}
namespace Translation
open Planet Scribe
variable [Fintype V]
set_option quotPrecheck false
local notation "Ψ"=> Whole V
variable (T:V→R.Mode) (f:Ω→V→ℂ) (hp:∀ i,(T i).val.Nonempty) (hO:∀ i v,v∈(T i).val → s' v⊆ s i)
local notation "P" => fun x:Ω=> morph T (f x) hp
variable {q:Ray R}{q':Ray (Whole V)}(S:Scribe Ω J G n (Whole V)) (r:Rental q)(r':Rental q')
noncomputable def scribe : Scribe Ω J G n R where
 tag i:= stamp T (S.tag i)
 region:= S.region
 total:= S.total
 score x i:= falls T (f x) (S.tag i) • S.score x i
local notation "S'"=> (scribe T f S)
local notation "ζ"=> stamp T
variable {p:BudgetPoint}{A₀ A₁:ℝ}
include hp
lemma vocals (x:Ω)(j:J)(U:Config G n)(p:BudgetPoint) : (P x) (S.enters p x U j)=(S').enters p x U j:=by
 have hx: (S').render p x j U= falls T (f x) (S.tag j)* S.render p x j U:= S.render_shade (fun x i=> falls T (f x) (S.tag i)) ..
 unfold enters; rw [sent, hx,mul_comm];rfl
include hO
lemma aspects (h:S.Proper p s) : Scribe.Proper S' p s':= by
 let L(x i):=falls T (f x) (S.tag i); have hS:= h.shade L; refine ⟨hS.length,hS.sight,?_,?_,hS.total⟩; 
 · intro i v x U hν he'; have hz: Fits T (S.tag i).val:= by by_contra H; exact hν (by simp only [scribe,falls,if_neg H,zero_smul,Pi.zero_apply])
   change v∈ (stamp T (S.tag i)).val at he'; rw [stamp,dif_pos hz] at he'; obtain ⟨j,hj,hp⟩:= mem_biUnion.mp he'; exact Finset.Subset.trans (hO j v hp) (hS.owns _ j x U hν hj)
 intro i he x; by_cases ht: Fits T (S.tag i).val; swap; · simp only [scribe,falls,if_neg ht,zero_smul]
 suffices ht: S.tag i= (Ψ).quiet by unfold Translation.scribe; dsimp only; rw [h.quiet i ht, smul_zero]
 by_contra hV; obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr (fun h'=>(hV (Subtype.ext h'))); obtain ⟨a,ha⟩:=hp j; have hx:a∈(stamp T (S.tag i)).val:= by rw [stamp, dif_pos ht]; exact mem_biUnion.mpr ⟨_,hj,ha⟩
 rw [show stamp T (S.tag i)= _ from he] at hx; exact Finset.notMem_empty _ hx
-- weight-bearing.Names
omit hp hO
def Check (q':Ray (Whole V))(q:Ray R)(A:ℝ) : Prop:= ∀ x i,S.score x i ≠ 0 → q (stamp T (S.tag i))* ‖falls T (f x) (S.tag i)‖ ≤ A*q' (S.tag i)
def News (q':Ray (Whole V))(q:Ray R)(A:ℝ) : Prop:= ∀ i x,q (stamp T i)* ‖falls T (f x) i‖ ≤ A*q' i
lemma News.all {q' q A}(h:News T f q' q A) : Check T f S q' q A:= fun x i _=> h _ x
abbrev drawer_ (q':Ray (Whole V))(q:Ray R)(A:ℝ) (i:(Whole V).Mode): ℝ:= A*q' i/q (stamp T i)
def hCheck (q q':Ray (Whole V)) : Prop:= q' ≤ q -- unused
-- specialized.IN.Current Alpha Lo.Temp.
include r r'
lemma stakes (hz:0≤A) (i:(Whole V).Mode):0 ≤ drawer_ T q' q A i:= div_nonneg (mul_nonneg hz (r'.pos _).le) (r.pos _).le
lemma funds (h:S.Spend p q' a B) (hv:Check T f S q' q A)(hz:0≤A): Scribe.Spend S' p q a (A*B) := by
 obtain ⟨u,hu,hU⟩:=h; let z:= drawer_ T q' q A; let l(i):= z (S.tag i)*u i; have hh i:0≤ l i:= mul_nonneg (stakes T r r' hz _) (hu.nonneg _); refine ⟨l,⟨hh, fun x i j hj=> ?_⟩, fun i=>?_⟩
 · let p':= S.tag i; change p.supBounds j (S.region i) (falls _ _ p' • S.score x i) _; by_cases hy:S.score x i≠0; swap; · rw [not_not.mp hy, smul_zero]; exact Push.Local.bound_weaken (Extra.Histories.regular0 ..).2 (hh i)
   refine Push.Local.bound_weaken (Next.Foundations.bound_smul (falls T (f x) p') (hu.bound x i _ hj)) (mul_le_mul_of_nonneg_right ?_ (hu.nonneg i)); unfold z drawer_; apply (le_div_iff₀ (r.pos _)).2; rw [mul_comm]; exact hv x i hy
 convert! budget_scale hz (hU i) using 1; ext j; simp only [scribe,l,z,drawer_]; split_ifs <;> field_simp [(r.pos (stamp T (S.tag j))).ne'] <;> ring
include hp
noncomputable def lift (K:Source G n Ω (Whole V)) : Source G n Ω R:= fun x i U=> morph T (f x) hp (K x i U)
variable {K': Source G n Ω (Whole V)} (hX:Night X s K' q' t A₁) (hA:0≤ A)
local notation "Γ"=> Translation.lift T f hp K'
include hX hO r r' hA
lemma silver (he:News T f q' q A): Night X s' Γ q t (A*A₁):= by
 -- transport at ANY weights. Need charge projections even zero and overlaps. Keep original layout for some uses.
 obtain ⟨g,hg,hG⟩:= hX.cost; let V' (x:Ω):= P x;
 constructor
 · intro x; let W:= P x; let g' :=hX.policy x; constructor
   · intro i; have hx:=g'.align i;
     refine ⟨fun U V hp hy=> congr_arg W (hx.travel U V hp hy), ?_,fun s U=>congr_arg W (hx.worth s U),fun U=>?_⟩
     · intro p; unfold lift; simp_rw [part]; refine Finset.measurable_fun_sum _ (fun i _ =>?_) ; split; exact ((hx.visible i).mul measurable_const); exact measurable_const
     intro p hp v hv; unfold lift at hp; rw [part] at hp; obtain ⟨z,-,hz⟩:= exists_ne_zero_of_sum_ne_zero hp; split at hz; swap; · simp at hz
     rename_i he'; have hy: Fits T z.val:= by by_contra h; exact hz (by simp only [falls,if_neg h,mul_zero])
     rw [he',stamp,dif_pos hy] at hv; obtain ⟨q,hq,hV⟩:= mem_biUnion.mp hv; exact Finset.Subset.trans (hO q v hV) ((hx.owns U) z (left_ne_zero_of_mul hz) q hq)
   · intro i v hK; exact g'.beacon i v (fun he=> hK (show morph _ _ hp (K' x i v)= _ from (congr_arg _ he |>.trans (map_zero W)))) -- Ψ instance
   intro i U; exact (preserveQ T _ hp _).trans (g'.quiet ..)
 let W:=drawer_ T q' q A; have hh(i):0≤ W i:= stakes T r r' hA i; let Y:(ℕ→Ray R):=fun i v=> ∑ j: (Ψ).Mode,if v=stamp T j then W j * g i j else 0 -- precedence
 let hb i j : 0 ≤ Y i j:= Finset.sum_nonneg fun l _=> by split; exact mul_nonneg (hh _) (hg.1 _ _); rfl
 refine ⟨Y, ⟨hb,fun i=>?_ ⟩,fun x i U v=>?_⟩
 · convert! budget_scale hA (hg.2 i) using 1; ext j; dsimp only [Y]; split; rotate_left; · rw [mul_zero]
   have hj: Parabola.bill q (Y j)=A* Parabola.bill q' (g j):= by
      unfold Parabola.bill Y; simp_rw [mul_sum]; rw [Finset.sum_comm]; refine sum_congr rfl (fun i hI=>?_); rw [Finset.sum_eq_single (stamp T i)]; rotate_left
      · intro a ha hj; rw [if_neg hj,mul_zero]
      · simp
      rw [if_pos rfl]; unfold W drawer_; field_simp [(r.pos (stamp T i)).ne'] <;> ring
   rw [show _=_ from hj,mul_assoc]
 · unfold lift; rw [part]; refine (norm_sum_le ..).trans (sum_le_sum ?_); intro j _; by_cases hz:v=stamp T j; swap; · rw [if_neg hz,if_neg hz,norm_zero]
   rw [if_pos hz,if_pos hz,norm_mul,mul_comm]; refine mul_le_mul ?_ (hG x i U j) (norm_nonneg _) (hh j); apply (le_div_iff₀ (r.pos _)).2; rw [mul_comm]; exact he j x
end Translation
end YM.Qlocal.Reckoner
