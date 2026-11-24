import YM.LocalLTE.Pool.Soft
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
local notation "W" => (bank n G M)
local notation "P" => iceCap (n:=n) G M p c x κ
variable (hs : Reliable G κ k) (hG:G.Simple)(hn:20<n.val) (hb:Decent c p)
-- Use βhat = t. Set χ models rates unit. 
variable (η:ℝ) (L:Side)
variable (ht : 1 ≤ t) (hx: ‖x‖≤2*t) (hd:c.direct≤1)(hG:G.Simple)(hn:20<n.val)(hP: p.threshold ≤ Start.threshold G p.order p.power) (ha:4 ≤ p.B)
-- rates extra. choose Λ_j. pay Price tψ small.History. Psi before Tor.
variable (he:η>0) (hh: 2*t*Start.item G p≤ η*t^(chip 0))(hv:∀ j:ℕ, j≤M → 2*t*(turnFee p*(betaF G t L)^(Urns.dust j-1))≤ η*t^(chip (j+1)))
variable (hW:∀ j:ℕ,j≤M→∀ (o:PlaqAxes), p.supBounds (0:Site n) (neighbors 4 0) (residual G (0,o)-glaze G o κ j) ((betaF G t L)^(Urns.dust j-1)))
local notation "P₀"=> Start.weight c x
include hx hd hP hW hG hs hn hh he ht hv
variable {e γ γ' α β : ℝ}
include ha
open Extra.Iteration Quotes
open Payments
variable (hc : kettleP p M η ≤ 1)
include hc
lemma books : ∃ f:ℕ→ ℝ,(∀ i,p.supBounds ((W).reg i).site ((W).reg i).support ((P).regular i) (f i))∧ anchored p (W|>.reg) (fun i=> f i*East.bloom t (age n M i)) (t^(chip 0)):=by
    obtain ⟨v,h,hP⟩:= Frost.bankCoins G M p c hs hG hn η L ht hx hd hP ha he hh hv hW; exact ⟨v,h,fun i=>budget_loosen (hP i) (mul_le_of_le_one_left (Real.rpow_nonneg (zero_le_one.trans ht) _) hc)⟩ -- order
omit hd hP ha hx hh he ht hc hv hG hs hn hW
lemma pitched (hl:Loan p (t/2) α β γ)(hd: Decent c p)(hx:t/2≤ x) : ∃ g:ℕ→ℝ, hardCost p W g (Real.exp (-β)*(Real.exp γ-1)) ∧ ∀ i (U:Config G n), ‖(P).forced i U‖ ≤ g i:=by
    let v:= Start.cash n p α; let s:= Real.exp (-β); let f i:=s*v i; refine ⟨f,⟨fun i=>mul_nonneg (Real.exp_nonneg _) (Start.cash_pos _),fun x=>?_⟩,fun i U=> Start.forced_money hd hl.forced hl.slope hl.allows hx i U⟩ -- y
    convert budget_scale (show 0 ≤ s from (Real.exp_pos _).le) (hl.packets.hit (n:=n) x) using 2 with i; unfold f; change (if x ∈ Start.extent n i then s*v i*Real.exp _ else 0)= _; split; exact mul_assoc ..; exact (mul_zero _).symm
open East
include hP ha hx hh he ht hc hv hG hs hn hW hb
lemma streamers (hl: Loan p (t/2) α β γ) (hr: Rates p.B e (Real.exp (-β)*(Real.exp γ-1)) (Frost.soft p η t) β)(hp:t/2 ≤ x) : Ingredients W P p (t^(chip 0)) e:=by
     obtain ⟨f,h,hf⟩:= Frost.books (κ:=κ) G M p c hs hG hn η L ht hx hb.direct hP ha he hh hv hW hc
     obtain ⟨g,hg,hG'⟩:= Frost.pitched G M p c hl hb hp
     obtain ⟨q,hq,hQ⟩:= Frost.haunt (G:=G) (x:=x) (κ:=κ) M p c η ht hx hb.direct hP ha he hh -- edit
     refine Payments.tender (Frost.fitsH _ _ _ _ hs hG hn hb) ⟨f,h,fun i=>?_⟩ hg hq (fun i U=>⟨hG' i U,hQ i U⟩) hr -- edit
     refine budget_mono (hf i) (fun i=> ?_) (fun j=> ?_)
     · split; exact mul_nonneg (Real.exp_nonneg _) (h _|>.1); exact le_rfl
     change (if ((W).reg j).site=i then p.mass _ _ else 0)≤_; split; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (h j|>.1) (East.bloom_bill ht _)) (Real.exp_nonneg _); exact le_rfl
-- propagate tags. radius all.Q remarks.N variant
open Rack
abbrev trunkTag (n:Side)(j:ℕ)(i:ℕ):ℕ:=match (regularKeys n i).2 with | Sum.inl i=> Frost.age n j i | Sum.inr _=> j+1
local notation "K"=> (Frost.trunkTag n M)
local notation "Z"=> finish (Design.top G c) c p W P x 0
lemma seed : Coup.License M (finish (Design.top G c) c p W P x 0) κ t (Frost.trunkTag n M) 4:=by
    let g:= iceCap (n:=n) G M p c x κ; let Y:= bank n G M; let Z':= (finish (Design.top G c) c p W P x 0); let X := Z'.activities; let v:= Rack.upE Y
    have hx' i: X.reg (v i)= Y.reg i ∧ X.E (v i)=g.regular i ∧ K (v i)= age n M i:=by refine ⟨Rack.reg_up Y i, stuffed v _ i,?_⟩; unfold Frost.trunkTag v Rack.upE; simp only [Progress.DirectedRecipe.book]
    obtain ⟨f,h,hF⟩:= Frost.books G M p c hs hG hn η L ht hx hb.direct hP ha he hh hv hW hc -- edit
    -- Budget includes weights.X.fill. Use helpers
    refine ⟨⟨fun i=> bloom_bill ht _,stuff v f,fun i=>?_,fun i=>?_⟩,fun i hi=>?_,fun {i} hi hp=>?_⟩
    · by_cases hy:i∈Set.range v; swap; · rw [show (Z).activities.E i=0 from blank v _ hy,blank v _ hy]; exact Start.zero_bound
      obtain ⟨i,rfl⟩:=hy; change p.supBounds (X.reg _).site (X.reg _).support (X.E _) _; rw [(hx' i).1,(hx' i).2.1,stuffed]; exact h i
    · apply transfer_budget v ?_ ?_ (hF i); swap
      · intro j hj; rw [blank _ _ hj,mul_zero]; simp [BudgetPoint.mass]
      intro j; rw [stuffed]; dsimp only; rw [(hx' j).2.2]; change (if (X.reg (v j)).site=i then p.mass (X.reg (v j)|>.support) _ else 0)=_; rw [(hx' j).1, mul_comm (East.bloom ..) (f j)]
    · by_cases hl:i∈Set.range v; swap; · change ∃ k≤4, LocalLTE.FrameBox.Polynomial _ κ _ _ (X.E i); rw [show X.E i=0 from blank v _ hl]; refine ⟨0,Nat.zero_le _,cane _,?_⟩; exact Price.rp_zero _
      obtain ⟨i,rfl⟩:=hl; change ∃ k≤4, LocalLTE.FrameBox.Polynomial _ κ (X.reg _).site _ (X.E _); rw [(hx' i).2.2,(hx' i).2.1,(hx' i).1]; let j:= age n M i; have hi':j≤M:=by unfold j; exact (hx' i).2.2 ▸ hi
      unfold g; rw [reggo]; split; next hp=>
         let a:=name (Card M n) i; let q:= a.2; let X':Art (ew (0:Site n)) 4:= ⟨cane _,3,rfl,by omega,by omega⟩
         let D:= X'.turn (boat q) (ew q.native) (shiftE q) (sp_k q); let V:=D.grove
         have hp (j:ℕ): Replicated V 3 κ (pie j+1) (Frost.draft G q κ j):= Price.rotatedG X' _ (boat q) _ (shiftE _) (sp_k q) hs ⟨_,rfl⟩ -- edit
         refine ⟨3,by omega, V, Price.rp_scale V (Start.weight c x) ?_⟩; change Replicated V 3 κ (pie j+1) (Frost.rota G q j M κ); unfold rota; rw [if_neg (show j ≠ M+1 by omega)]; split
         next h=> rw [h]; exact hp 0
         next h=> exact rp_sub V (hp _) (rp_raise V (hp _) (by unfold pie; omega)) -- edit
      exact ⟨0, Nat.zero_le _, cane _, rp_zero _⟩
    · by_cases hl:i∈Set.range v; swap; · exact False.elim (hp (blank v _ hl))
      obtain ⟨i,rfl⟩:= hl; change (X.reg (v i)).support ⊆ neighbors 4 (X.reg (v i)).site; rw [(hx' i).1]; exact Finset.Subset.refl _
end YM.WilsonStartup.Frost
