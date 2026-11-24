import YM.AllOrder.Carillon.Essence
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Carillon
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "B" => radiusB p
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)
open Match Refrain
-- Shaped estimation recycled, HOZ. no modification of K.Also installs alternative polymer by Path tune, not Worker reprice assumptions.
variable (χ:Chi)(H) (P:BudgetPoint)(β γ:ℝ) (α:ℝ)
local notation "D"=> plusone H Θ χ α
local notation "X₀"=> posting P H
local notation "Γ"=> organ H χ β γ
section first
variable {t u σ C Λ:ℝ} (h:T.down.Bounds T.low σ C Λ) (he:Collection.Local (posting P H) P (plusone H (Match.staple (H:=H) (J:=H) rfl rfl rfl) χ α) t u)
 (hq: preExponent P /P.B≤ σ/2) (hp:WilsonStartup.Decent T.low P)
local notation "w"=> octaveNeed G P T.low σ C Λ R.beta α
local notation "p'"=> octaveNeed G P T.low σ C Λ β γ
def payment (P:BudgetPoint)(G:Gauge)(l:Clip)(σ C Λ t β γ β' γ':ℝ):=t+turnFee P*(octaveNeed G P l σ C Λ β γ+ octaveNeed G P l σ C Λ β' γ')
def port : Magazine H→ Config G c→ℝ:= Sum.elim (fun _=>0) (sounding T.down T.low β γ)
include he
-- check arg χ unused
lemma dilate (s:Signed)(b:Site c)(A:Magazine H→ Config G c→ℝ):Nonempty (((X₀).read ⟨choir A ∘ pennant H,(D).hardRead⟩).Moves s b):=by
 obtain ⟨q⟩:= he.transforms s b; let v:= pennant H; let t:= whirl (ι:=Magazine H) (n:=c) s b; let G':=congo v t; let L i:= spirit (scaleT P H) A s b (v i); refine ⟨⟨G',q.kp,?_,?_,q.forced_support,q.forced_inventory,q.forced_tests,?_,q.valuesK⟩⟩
 · intro i; change (revolve (scaleT P H) (v (G' i))).site=_; rw [show v (G' i)=_ from perch v t i]; exact (L i).1
 · intro i; change (revolve (scaleT P H) (v (G' i))).support=_; rw [show v (G' i)=_ from perch v t i]; exact (L i).2.1
 intro i x; change choir A (v (G' i)) x=_; rw [show v (G' i)=_ from perch v t i]; exact congr_fun (L i).2.2 x
omit he
include h hp hq
lemma prime : ∃ f: Magazine H→ℝ, Quotes.early P (scaleT P H) f (p') ∧ ∀ i,P.Regular (scaleT P H i|>.support) (port H β γ i) ∧P.supBounds (scaleT P H i|>.site) (scaleT P H i|>.support) (port H β γ i) (f i):= by
 obtain ⟨f,hv,hQ⟩:= stanzaReady (n:=c) T.down T.low P β γ h hp hq; let g:Magazine H→ℝ:= Sum.elim (fun i=>0) f; refine ⟨g,fun i=>?_,?_⟩
 · have hh : SumBudget (fun x:H.fragrances=> if (locate H x).site=i then (0:ℝ)*Real.exp (preExponent P*coverNumber P.B (locate H x|>.support)) else 0) 0 := (by simp only [zero_mul,ite_self]; exact ⟨fun _=> le_rfl, summable_zero, tsum_zero.le⟩); exact Cost.enlarge (Cost.sum hh (hv i)) (zero_add _|>.le)
 intro i; rcases i with i|i; exact ⟨Progress.DirectedRecipe.unspent ..,Progress.DirectedRecipe.no_cost ..⟩; exact hQ i
omit h hp hq in
private lemma plusBudget {ι:Type}{p:BudgetPoint}{t:ι→RegularAddress c}{a b:ι→ℝ}{A B':ℝ}(h:Quotes.early p t a A) (hv:Quotes.early p t b B') : Quotes.early p t (a+b) (A+B'):= by
 intro i; convert budget_plus (h i) (hv i) using 2 with x; dsimp only [Pi.add_apply]; split_ifs <;> ring
include h he hp hq
lemma scope : Collection.Local X₀ P Γ (payment P G T.low σ C Λ t R.beta α β γ) u:= by
 let A:= X₀; let V:= Γ; let f:= fun (t k:ℝ)=> choir (port H t k) ∘ pennant H; let g:=f R.beta α; let h':=f β γ; have hx : V.logRead=(D).logRead+(h'-g):=by
    ext i U; let v:=pennant H i; change Rim c*hymn H χ β γ v.2 _=_+(Rim c*(port H β γ v.2 _) - Rim c * (port H R.beta α v.2 _)); change _ = Rim c* (opus H Θ χ α v.2 _)+(Rim c * (port H β γ v.2 _)-_); unfold hymn opus port; cases v.2 <;> simp only [Sum.elim] <;> (try simp only [Pi.zero_apply,mul_zero,sub_zero,add_zero])<;> ring
 obtain ⟨ψ,hD,hd⟩:= he.cheap; let k := P.order; let S:= scaleT P H
 obtain ⟨p,hp',hl⟩:= prime H P R.beta α h hq hp; obtain ⟨s,hs,hy⟩:= prime H P β γ h hq hp
 have hY: ∃ u', Quotes.early P S u' (w+p')∧ ∀ i,P.Regular (S i).support (port H β γ i-port H R.beta α i)∧P.supBounds (S i).site (S i).support (port H β γ i-port H R.beta α i) (u' i):= by
    refine ⟨s+p,fun i=>?_,fun i=> ⟨VerifiedReset.reg_sub (hy i|>.1) (hl i|>.1), VerifiedReset.sup_sub (hy i|>.1) (hl i|>.1) (hy i|>.2) (hl i|>.2)⟩⟩; rw [add_comm s p]; exact plusBudget hp' hs i
 obtain ⟨u,hg,ht⟩:=hY; obtain ⟨hh,hB⟩ := Song.spiral S (fun i=> port H β γ i - port H R.beta α i) _ (fun i=>(ht i).1) (fun i=>(ht i).2) hg;
 let u' (i:ballad H):ℝ:= (Rim c)*(turnFee P*u i.2); let U':= h'-g; have hW(i:ℕ) : P.Regular (A.reg i).support (U' i)∧ P.supBounds (A.reg i).site (A.reg i).support (U' i) (u' (pennant H i)):= by
    rw [show U' i= _ from (?_ : _=(Song.choir (fun i=> port H β γ i-port H R.beta α i) (pennant H i)))]; exact hh _
    ext1 x; unfold U' h' g f choir; dsimp only [Function.comp_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring
 let L:= hW; have hx i: V.logRead i=(D).logRead i- ((-1:ℝ) • U' i):= by rw [hx]; simp; rfl
 have hv i:= CouplingShape.reg_scale (-1) (L i|>.1); refine ⟨fun i=> ?_,⟨he.family.sym,he.family.symtest,he.family.meas,he.family.meas_test,he.family.reads,he.family.reads_test,he.family.permit⟩, fun s b=> dilate _ _ _ _ he s b (hymn H χ β γ), ⟨fun i:ℕ=>ψ i+u' (pennant H i),?_,?_⟩,he.expensive⟩
 · change P.Regular (A.reg i).support (V.logRead i); rw [hx]; exact VerifiedReset.reg_sub (he.smooth i) (hv i)
 · intro i; change P.supBounds _ _ (V.logRead i) _; rw [hx]; refine VerifiedReset.sup_sub (he.smooth i) (hv i) (hD i) ?_; simpa only [abs_neg,abs_one,one_mul] using CouplingShape.sup_scale (-1) (L i|>.2)
 exact plusBudget hd (b:=u'∘(pennant H)) (show Quotes.early P (X₀).reg (u'∘(pennant H)) _ from fun i=> Cost.equiv (pennant H) (hB i))
end first
end YM.AllOrder.Carillon
