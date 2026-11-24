import YM.RegulatorIR.Epoch.Calendar

/-!
# Run histories with overlap. Read K in Meter theorem.
Constants *ahead* on raw bins. Pinned construction shape theorem under
budget conditions, no summability requirements beyond. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Epoch
open Function Set Filter Finset Lattice RG Gauge Budget Budget.Packet Budget.Tuple Budget.Layer Geometry Uniform YM.RegulatorIR.Ledger Step Taping Precision Laurent Bloch Oracle Quadratic ENNReal
open RegulatorIR.Momentum (extent postage lamp Held)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y I:Type}{n x:ℕ}

def amount (K:Packet (Long X) (n+1))(u:ℕ):ℝ≥0∞:= ⨆ i, quota (RegulatorIR.Momentum.anchored i K) (RegulatorIR.Momentum.wall (Momentum.area i) 1 u) -- area_m fix
lemma amount_cap {K:Packet (Long X) (n+1)}{u:ℕ} {c:ℝ≥0∞} (hp:Held K u c):amount K u≤c:=iSup_le hp
lemma bound_h (K:Packet (Long X) (n+1))(u):Held K u (amount K u):= fun v=> le_iSup (fun i=> quota (RegulatorIR.Momentum.anchored i K) (Momentum.wall (Momentum.area i) 1 u)) v
section populate
variable {G: Gauge}
def kernel_cap (G : Gauge)(u:ℕ)(σ Ω:ℝ):ℝ≥0∞:= (Fintype.card (FreeResolvent.PAC G 1):ℝ≥0∞)*ENNReal.ofReal (FreeResolvent.kinPrice σ Ω)*ENNReal.ofReal (scar σ u)
lemma assured (u σ Ω):kernel_cap G u σ Ω≠⊤:=by unfold kernel_cap;finiteness
variable {B: Precision.Bed} {α σ Ω:ℝ} {C:Clip}
lemma current_read (G : Gauge) (H:Hall B σ Ω α C) : Held (lamp (crust G B)) x (kernel_cap G x σ Ω):=by
 intro i
 let k:= crust G B; let q:= kernel_cap G x σ Ω
 let g(z:Long G.ColorIndex):ℝ≥0∞:= RegulatorIR.Momentum.quotes i.1.1 z 1 x
 have he t : RegulatorIR.Momentum.wall (r:=1) (Momentum.area i) 1 x t=g (t 0):=by unfold RegulatorIR.Momentum.wall;rw [Fin.sum_univ_succ];simp [g,RegulatorIR.Momentum.quotes,Momentum.area]
 rw [show RegulatorIR.Momentum.wall (r:=1) (Momentum.area i) 1 x= _ from funext he]; rw [← quota_perm (Pert.Bulk.identify _).symm];
 change quota (k i) (fun z=> g z) ≤ q
 have hv(z): g z≤ liftsE ((linksQ G).boom i) ((linksQ G).boom z) σ * ENNReal.ofReal (scar σ x):=by
    let t:=size (i.1.1-z.1.1)
    have hp := ENNReal.ofReal_le_ofReal ((scars σ x H.pos).2 t)
    change (1+Momentum.award 1* extent _ )^x ≤ _
    simp_rw [Momentum.award,Nat.cast_one,inv_one,one_mul,one_smul,liftsE,← ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm _ (scar σ x)];
    refine le_trans ?_ hp; change (1+(t:ℝ≥0∞))^x ≤ ENNReal.ofReal _;rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_add (by positivity: (0:ℝ)≤1+t) (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one,ENNReal.ofReal_natCast];exact pow_le_pow_left' le_self_add _
 apply (quota_mono _ hv).trans
 rw [quota_raised]; exact mul_le_mul_left (crust_price G B H.stripP.2.1 H.pos.le H.paid i) _
lemma diff_budget (G:Gauge) (H:Hall B σ Ω α C) {M:Bed}{s:Clip}{η p q:ℝ}(V:Hall M η p q s) : amount (lamp (crust G B - crust G M)) x ≤ kernel_cap G x σ Ω + kernel_cap G x η p:=by apply amount_cap; intro v; exact (quota_sub (RegulatorIR.Momentum.anchored v (lamp (crust G B))) _ _).trans (add_le_add (current_read G H v) (current_read G V v))
end populate
namespace League
variable {W W':Type}{M:W→ℕ}{P:Page M→Side}{N:W'→ℕ}{Q:Page N→Side}{K:KernelChoices} (S: Circuit M P) (T:Circuit N Q)(F:Program K)
-- any overlapping Ly-stage and scale authorization.
structure Section (S: Circuit M P)(T: Circuit N Q) where
 cast_r : W→W'
 connects : Page M→Page N
 from_w p: (connects p).bindW=cast_r p.bindW
 fly : Flap M→ Flap N
 previous i : connects i.prev= (fly i).prev
 next i: connects i.next= (fly i).next
 pact i : T.pactP (fly i)= S.pactP i
-- Admitting two schedules. Scales frozen K. top branch.Cover mobility not blocked.
variable {S T} (A:Section S T)
-- invoices require rows.K and open startup polls
def shareP (G:Gauge)(S:Circuit M P)(u:ℕ)(F:Program K)(i:Page M) :ℝ≥0∞:= kernel_cap G u (F.receipt.α (S.J i)) (F.receipt.Ω (S.J i))
def beginsP (G:Gauge)(S:Circuit M P)(u:ℕ)(F:Program K)(i:Flap M):= pack_c G u (F.receipt.α (S.J i.prev)) (F.receipt.Ω (S.J i.prev))
-- tuple spends G. UV rate choose. `G0` far.K.Holder`. all parameters local before.N.
structure Counselor (G:Gauge)(S:Circuit M P)(u:ℕ)(F: Program K)(B:Marked M) (γ:ℝ): Prop where
   shapeS i:B.gap i= (S.sizeL i).val
   capital : B.Structural
   depth : 3≤u
   terms (i:Flap M):3 ≤ S.J i.prev-2
   currency : Poly B.age_t (shareP G S u F)
   cut (i:Flap M): RegulatorIR.Momentum.fore_c G.ColorIndex 1 u 3 (beginsP G S u F i)* RegulatorIR.Momentum.award (S.sizeL i).val≤B.coin (-γ) i
variable (B : Marked M)(G : Gauge){θ γ:ℝ}{p:ℕ} (Z: Counselor G S p F B γ)

def pipeline (G:Gauge)(D : Program K)(i:Page M):= lamp (crust G (S.tables D i) - crust G (T.tables D (A.connects i)))
include Z
lemma linked (i:Flap M): amount (pipeline A G F i.next) p ≤ B.coin (-γ) i * amount (pipeline A G F i.prev) p :=by
 have hx:= A.pact i
 let a:= A.fly i
 have hv': T.J a.prev=S.J i.prev:=congr_arg Patch.J hx
 have hℓ':T.sizeL a= S.sizeL i:= congr_arg Patch.L hx
 let HP:= S.honored F i.prev;let HC:= S.honored F i.next;let HF:= T.honored F a.prev;let HV:=T.honored F a.next
 let v:=beginsP G S p F i
 let c:= amount (lamp (crust G (S.tables F i.prev)-crust G (T.tables F a.prev))) p
 have hc:c≠⊤:= ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨assured _ _ _,assured _ _ _⟩) (diff_budget G HP.card HF.card)
 have hf:v≠⊤:= pack_c_f G _ _ _
 let D:= T.tells F a
 have hh: ∃ H:Cross (S.sizeL i) (Exterior.TypeFace 1) (Exterior.TypeFace 1), BidP (S.pactP i) K (T.tables F a.prev) (T.tables F a.next) H (F.receipt.α (T.J a.prev)) (lesser (F.receipt.Ω (T.J a.prev)) (T.sizeL a)) ∧ RegulatorIR.Momentum.PriceW (Oracle.ruling (S.pactP i) G H) (S.sizeL i).val p 3 v:=by
    change ∃ H:Cross (S.pactP i).L (Exterior.TypeFace 1) (Exterior.TypeFace 1), BidP _ _ _ _ _ _ _∧ RegulatorIR.Momentum.PriceW _ (S.pactP i).L.val _ _ _
    rw [← hx]; have ht:= T.predicted F a; have hQ: RegulatorIR.Momentum.PriceW (Oracle.ruling (T.pactP a) G D) (T.sizeL a).val p 3 v:= by
       unfold v beginsP; rw [← hv']; exact discount_p T F G a 3 p (hv'.symm ▸ (Z.terms i))
    exact ⟨D,ht,hQ⟩
 obtain ⟨H,h,h'⟩:=hh
 have hz:= RegulatorIR.Momentum.km_paid G K (S.pactP i) (S.tells F i) H HP.card HC.card HF.card HV.card (S.predicted F i) h p v hf Z.depth (discount_p S F G i 3 p (Z.terms i)) h' c hc (bound_h _ p)
 unfold pipeline; rw [A.previous,A.next]; exact (amount_cap hz).trans (mul_le_mul_left (Z.cut i) c)
open Reserve
lemma progressing (g:0≤ θ)(he:θ<γ)(H: Poly B.age_t (shareP G T p F ∘ A.connects)):
 Carry B.age_t (peak_M B θ) (fun i=> amount (pipeline A G F i) p) :=by
 have ht:Poly (B.age_t.us (Page.opening M)) (fun i=> amount (pipeline A G F (Page.opening M i)) p):= ((Z.currency.add H).us (Page.opening M)).mono fun i=> diff_budget G (S.honored _ _).card (T.honored _ _).card
 refine B.damper _ (fun _=>0) θ γ Z.capital he g (tactics B θ) (Carry.zeroQ _) ?_ (fun i=> le_trans (linked F A B G Z i) (by simp))
 simp only [Function.comp_def,peak_M,maskA,Page.opening,sub_self,zero_mul,Real.exp_zero, ENNReal.ofReal_one]; exact Carry.regular ht
end League
end YM.RegulatorIR.Epoch
