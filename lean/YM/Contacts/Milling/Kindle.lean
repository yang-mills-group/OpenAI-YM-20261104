import YM.Contacts.Milling.Shine
import YM.Progress.JOINT_CALENDAR.Germs
noncomputable section
namespace YM.Contacts.Milling.Lumen
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent
open scoped Topology BigOperators Classical Matrix NNReal ContDiff Matrix.Norms.Frobenius
variable {α : Type}{B : Bed}{n:Side}{G:Gauge}
private abbrev Shape (G : Gauge):= (Option Axis × Dye G)
def rose (G:Gauge)(x:Shape G) : Node (Dye G):=(x.1.elim 0 (Lattice.step ·),x.2)
def people (G:Gauge)(v:Option Axis)(i:Axis): House.Dir (Shape G) →L[ℝ] G.Color := LinearMap.toContinuousLinearMap { toFun p := WithLp.toLp 2 fun j=> p (v,coord i,j), map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
def rook (G:Gauge)(x:House.Dir (Shape G)) := ∑ p:PlaqAxes, let a:=p.val.1; let b:=p.val.2; G.price (G.lieExp (people G none a x)* (G.lieExp (people G (some a) b x)* ((G.lieExp (people G (some b) a x))⁻¹ * (G.lieExp (people G none b x))⁻¹)))
lemma rook_spec (x:Link G n) : (energy∘input G n) x=∑ i:Site n, rook G (load (rose G) i x):= by
  unfold Function.comp Wilson.energy; rw [Fintype.sum_prod_type]; refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _=>?_); let a:=p.val.1; let b:=p.val.2; let P:=load (rose G) i x; dsimp only; unfold faceValue square; refine congr_arg G.price ?_; simp only [travel, Step.pos_read, Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one];
  have hp (a):people G none a P= arm G n 1 x (i,coord a):= by ext1 j; change x (wrap n 0+i,_)=x _; rw [map_zero,zero_add]; rfl
  have hf a b: people G (some a) b P=arm G n 1 x (i+step a,coord b):= by ext1 j; change x (wrap n (Lattice.step a)+i,_) = x _; rw [wrap_step,add_comm i]; rfl
  -- rewrite
  simp only [encode_link]; erw [hp,hp,hf,hf]; erw [show i+step a+step b-step a=i+step b by abel,show i+step a+step b+ -step a-step b=i by abel]
lemma rook_ana (G:Gauge): AnalyticAt ℝ (rook G) 0 := by
  have ht (v i): ContDiff ℝ ω (fun p=> G.mat (G.lieExp (people G v i p))) := G.exp_jet.comp (people G v i).contDiff
  have hv (v i): ContDiff ℝ ω (fun p=> G.mat (G.lieExp (people G v i p))⁻¹) := by simp only [G.mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (ht v i)
  unfold rook; apply ContDiffAt.analyticAt (ContDiffAt.sum _); intro i _; apply Work.F03.price_smooth; simp only [G.mat_mul]; exact ((ht _ _).mul ((ht _ _).mul ((hv _ _).mul (hv _ _)))).contDiffAt
abbrev firewood (G:Gauge)(r:ℕ) := aboard (rose G) (words (rook G) r)
def flare (G:Gauge): bore G := fun e r=> if r=e+2 then firewood G r else 0
lemma flare_frame (G:Gauge): Cradle (Dye G) (flare G):= ⟨⟨fun _ _=> by unfold flare; split; exact print_even _; apply Poem.empty, fun i r hi=> if_neg (by omega)⟩,fun x i r=>by unfold flare; split; exact aboard_hold _ _ _; exact fun _=>rfl,fun i=> if_neg (by omega)⟩
def flare_cost (G:Gauge) (s:ℝ≥0) (i r:ℕ):= cargo (rose G) s (words (rook G) r)
lemma flare_purse (G:Gauge)(s:ℝ≥0): Roof s (flare G) (flare_cost G s) := ⟨fun i r=>by unfold flare; split; exact aboard_summed _ _ _; exact (Pulse.Rooted.tranquility _).weaken (fun _=>le_rfl) (aboard_summed (rose G) s (words (rook G) r)|>.cash)⟩
lemma rootBase {v b:ℝ}{P:Clip} (hp: Floor B P n v b) (ht:B.diagonal.acts n=1): Radial.Stationary (energy ∘ input G n) ∧ (∀ x, jet (energy ∘ input G n) 2 x=x ⬝ᵥ (spindle G n B.metric *ᵥ x) / 2):= by
   have he:=Progress.Joint.energy_born (n:=n) (G:=G); apply torch_c (F:=energy ∘ input G n) (AnalyticAt.comp (f:=arm G n 1) (g:=fun a => energy (represent a)) (by rw [map_zero]; apply he.analyticAt) ((arm G n 1).analyticAt _)); intro x
   have hv := Progress.Joint.energy_limit B (arm G n 1 x) hp ht; unfold sample; simp only [sample,Function.comp_apply,input,map_smul]; suffices hp: x ⬝ᵥ (spindle G n B.metric *ᵥ x) = gaugeFiscal B (arm G n 1 x) (arm G n 1 x) by rw [hp]; exact hv
   erw [component_dot]; unfold spindle; simp_rw [component_mul]; rfl
lemma fuel (n:Side)(i r:ℕ)(x:Link G n): grate (hair (flare G) n) i r x= if i=0∧2≤r then jet (energy ∘ input G n) r x else 0:= by
   unfold grate hair flare; split_ifs with h h1 h2
   all_goals first| omega| rfl| skip
   · have hh : i=0∧2≤r:= by omega
     rcases hh with ⟨rfl,H⟩; letI : NeZero r:= ⟨by omega⟩; have hp: printShadow (firewood G r) n=ashore (rose G) (words (rook G) r) n:= focused (printFeeds (heritage (fun i=> aboard_hold _ i _) n)) (lower_onto n) (aboard_desc _ _ _); erw [hp]; rw [words_read,show energy∘input G n=(fun x=>_) from funext (rook_spec (n:=n) (G:=G)),loan_sum _ (fun i _=> ?_)]; swap; · exact starts _ (rook_ana ..) (load (rose G) i)
     apply sum_congr rfl; intro i _; rw [Garf.hash]; exact (woven (rook_ana G) _ x _).symm
   rw [printLull,parcel_nil]
lemma homeLit (L:Levels G)(N:Horizon L){T:MapPrices}(h:N.Suffices T)(j:ℕ) : Blazing (flare G) (N.H j j) := by
   let B:= N.H j j; let U (n:Side):= hair (flare G) n; have ht (n) :=rootBase (G:=G) (h.all j j le_rfl n) (h.top j n); refine ⟨flare_frame G, fun n=>⟨cradle_shape (flare_frame G),fun x=>?_⟩,fun n k i hi=>?_⟩
   · have hz:=fuel n 0 2 (G:=G) x; erw [if_pos (by decide),grate,if_pos (by decide), (ht _).2] at hz; exact hz
   let V:=wind (U n) (k+3) i; let p:= k+3-i; have he: AnalyticAt ℝ V 0:= wind_ana ..; have ht': Continuous V:= continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt)
   change Guards V p; by_cases h0:i=0; swap; · rw [show V=0 from funext fun x=> by unfold V wind; exact sum_eq_zero fun j _=> (fuel n i j x).trans (if_neg (fun u=> h0 u.1))]; exact ⟨continuous_const,analyticAt_const,fun _ _=>rfl,fun _ _=>rfl,by simpa only [Pi.zero_apply,sub_self] using (jet_bridge (f:=fun x:Swatch G n=>(0:ℝ)) (n:=p) analyticAt_const).2 (fun i j _=> jet_empty j i)⟩ -- p
   subst i; let E:= energy ∘ input G n; have hv : Pointwise E:= point_actual energy (starts _ Progress.Joint.energy_born.analyticAt (arm G n 1).toContinuousLinearMap) (fun a b=> energy_gauge b a) (fun a b=> energy_pull b a 0)
   have hh : Rays p (V-E) := valued p he hv.analytic (fun x i hi=> by unfold V U; rw [wind_jet,if_pos (by unfold p at *; omega),fuel]; split; rfl; symm; exact (jet_bridge hv.analytic).1 (rays_cast hv.analytic (ht n).1) x i (by omega))
   have hl (L:Link G n→L[ℝ]Link G n)(h:E ∘ L = E):V∘ (L:Link G n→Link G n)=V:= by
      apply instant (repeater (wind_controls ..) L) (wind_controls ..); let g:= merkin (he.sub hv.analytic) hh _ (L.analyticAt _) L.map_zero; convert g.sub hh using 1; ext x; change V (L x)-V x= V (L x)- E (L x)-(V x-E x); rw [show E (L x)=_ from congr_fun h x]; abel
   refine ⟨ht',he,fun u=> congr_fun (hl _ (funext fun x=> by unfold E Function.comp; rw [← stain_cons u x, energy_gauge])),fun s=> congr_fun (hl (orderTurn s) ?_), ?_⟩
   · ext x; change energy (input G n (flipCoords s ℝ x))=_; rw [← flip_links s,energy_pull]; rfl
   let P:= moveField (m:=n) (G:=G); let X:= ContinuousLinearMap.snd ℝ (BaseSites G n) (Link G n); let A:= (V-E) ∘ P; let C:= (V-E) ∘ X; have hp: Rays p (A-C):=(merkin (he.sub hv.analytic) hh _ moveField_analytic moveField_zero).sub (merkin (he.sub hv.analytic) hh _ (X.analyticAt _) X.map_zero)
   have hr : (A-C) =ᶠ[𝓝 0] fun a=>V (P a)-V a.2 := moveField_germ.mono fun a ha=> by
        have ht:E (P a)=E a.2:=(congr_arg Wilson.energy ha).trans (energy_gauge ..); change (V (P a) - E (P a)) - (V a.2-E a.2)=V (P a)-V a.2; rw [ht]; abel
   exact fun x=> (hp x).congr' ((along x).eventually hr) .rfl
end YM.Contacts.Milling.Lumen
