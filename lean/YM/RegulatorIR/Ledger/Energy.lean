import YM.RegulatorIR.Ledger.Ether

/-! Companion cover estimates, With a quantitative soft decay given by the
step row gains in the chosen gradient substitutions. Charging them separately
allows accounting for the single-mark estimates versus product telescope. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts)
variable {r e p u b m:ℕ}{c : Flap M→ℝ≥0∞}{d:Page M→ℝ≥0∞}{x:W→Room}{s:W→ℝ≥0∞}{L:Meter W}
variable (R:(w:Page M)→Orders (X w))

def ticket (d: Page M→ℝ≥0∞)(s:W→ℝ≥0∞)(w:Page M): ℝ≥0∞:= s w.bindW*(d w)⁻¹

/-- Common credit scale for positive-rank cover propagation. The skipped
charge `past` ↑L^p when a prior coefficient flows in. May use `sanctity`
if rank slightly below contraction range does not appear. -/
structure Softness (u:ℕ)(L:Meter W)(c:Flap M→ℝ≥0∞)(d:Page M→ℝ≥0∞)(α:ℕ): Prop where
  fund : S.Lead u c
  root : ∀ i,d i≠0
  limit : ∀ i,d i≠⊤
  cool : ∀ i,c i ^ α * d i.next ≤ d i.prev
  past : Poly (flapL M L) (fun i=>(d i.prev)⁻¹*d i.next)
  warm : ∀ i : Flap M,d i.prev≤d i.next
structure Imprints (u p m:ℕ)(x:W→Room) (d:Page M→ℝ≥0∞)(s:W→ℝ≥0∞)(α:ℕ)(L:Meter W) : Prop where
  -- R is a forced cover transmission, under its own exact Ward premise
  starts i : i ≤ p → ∀ r,0<r → Claim L (fun w=> S.coverQ x u (Page.opening M w)) (fun w=>ticket d s (Page.opening M w)) (fun w=> R (Page.opening M w) i r)
  force i : i ≤ p → ∀ r, Claim (flapL M L) (fun w:Flap M=> S.coverQ x u w.next) (fun w=> ticket d s w.prev) fun w=>R w.next i r - S.reportOut T R m w i r
  consent : ∀ w i,i ≤ p → (S.sight w).Way (R w.prev) i
  rank : ∀ w e,e≤p→ Within (e+m) (R w e)
  sanctity : ∀ w i j,i ≤ p → 0<j → j<α → R w i j=0
  compact : ∀ w, s w≠⊤
namespace ticket
lemma near (h₁:∀ w,d w≠0)(h₂:∀ w,s w≠⊤) (w) : ticket d s w≠⊤:=ENNReal.mul_ne_top (h₂ _) (ENNReal.inv_ne_top.mpr (h₁ _))
lemma worth (h₁:∀ w,d w≠0)(h₂:∀ w,d w≠⊤)(w:Page M): ticket d s w * d w = s w.bindW:= by rw [ticket, mul_assoc,ENNReal.inv_mul_cancel (h₁ w) (h₂ w),mul_one]
end ticket

lemma prior (T':(w:Page M)→Packet (X w) r)(h:Claim (coverL M L) (S.coverQ x u) d T') : Claim (flapL M L) (S.yard x u) (fun w=> d w.prev) (fun w=>T' w.prev):= by
 have h₀ : Claim (flapL M L) (S.camp.rooted (step_center M x) u) (fun w=>d w.prev) (fun w=> T' w.prev):= Claim.us h Flap.prev
 exact Post.few_cover (M:=S.camp) S.ridge_pos (l:=S.ridge) S.radius_climb h₀
variable {α:ℕ} (B:S.Primitive L p b)(N:S.Supplies T L p b)
   (G:S.Softness u L c d α)(I:S.Imprints T R u p m x d s α L)(hu:u ≤ b)

include B N G I hu
private lemma retained (w: Flap M)(he:e≤p): markQ (S.yard x u w) (R w.prev e r)≠⊤:= by
 have hc:=ticket.near G.root I.compact
 exact ne_top_of_le_ne_top (S.preserves T R B N (fun w i hi j hj=> Claim.cost (I.starts i hi j hj) _ (hc _)) hu m (fun w i hi j _=> Claim.cost (I.force i hi j) _ (hc _)) w.prev e he r) (Post.on_fewer (M:=S.camp) (x:=step_center M x) S.ridge_pos (l:=S.ridge) S.radius_climb w _)
lemma pruned
 (hp:∀ i j,Earlier e r i j →0<j→Claim (coverL M L) (S.coverQ x u) (ticket d s) fun w=> R w i j)(he:e≤p) : Claim (flapL M L) (fun w:Flap M=>S.coverQ x u w.next) (fun w=> ticket d s w.prev) fun w=>R w.next e r- S.lifts.bump (fun w=>R w.prev e r) w:=by
 have HH: Claim (flapL M L) (fun w:Flap M=>S.coverQ x u w.next) (fun w=>ticket d s w.prev) fun w=> S.reportOut T R m w e r -S.lifts.bump (fun w=>R w.prev e r) w:= Batch.beam_mark S.lifts (fun w=> T.bulk w.prev) (fun w=> R w.prev) (fun w=> GridStep.joint_vac_shape _ (T.cap_b B.grade _) (B.grade w)) (fun i hi j=> Post.work_fewer (M:=S.ceilingRoom) (l:=S.ridge) S.ridge_pos S.ridge_more (S.ceilingRoom.writes (S.lifts.fine_work (T.deposit N i (hi.trans he) j) (B.add_cost i (hi.trans he) j)) hu)) (S.lines_tag B hu) (S.get_drift B hu) (fun i j hi hj=> S.prior (fun w=> R w i j) (hp i j hi hj)) (fun _=> ticket.near G.root I.compact _) (fun w=> retained S T R B N G I hu w he) _
 convert Claim.add (I.force e he r) HH using 1; ext1 w; abel
lemma trimmed (hp:∀ i j,Earlier e r i j → 0<j → Claim (coverL M L) (S.coverQ x u) (ticket d s) fun w=> R w i j)(he:e ≤ p) : Claim (flapL M L) (fun w:Flap M=> S.coverQ x u w.next) (fun w=> ticket d s w.prev) fun w=> R w.next e r-updateQ (S.sight w).straight (R w.prev e r) 0:=by
 have hq : Claim (flapL M L) (fun w:Flap M=>S.coverQ x u w.next) (fun w=> ticket d s w.prev) fun w=> S.lifts.bump (fun w=> R w.prev e r) w -updateQ (S.sight w).straight (R w.prev e r) 0:= Batch.land (T:= fun w=> R w.prev) (F:=S.lifts) S.sight (fun w=>Premium.rooted (native _ (S.ridge_pos w) u) (x w.volW)) (fun i hi=> S.adv B hu i (hi.trans he)) (fun i hi j hj=> S.prior _ (hp i j (Or.inl hi) hj)) (fun w=> ne_top_of_le_ne_top (retained (r:=r) S T R B N G I hu w he) (quota_mono _ fun z=> (S.yard x u w).width_unit z)) B.ground (fun w=>I.consent w e he) (S.get_drift B hu)
 convert Claim.add (pruned S T R B N G I hu hp he) hq using 1; ext1 w; abel

private lemma finances (hp:∀ i j,Earlier e r i j → 0<j → Claim (coverL M L) (S.coverQ x u) (ticket d s) fun w=>R w i j)(he:e ≤ p)(hr:0<r) (hh:α≤r): Claim (coverL M L) (S.coverQ x u) (ticket d s) (fun w=>R w e r):=by
 let f(w:Page M):= markQ (S.coverQ x u w) (R w e r)
 let Z(w:Flap M):= updateQ (S.sight w).straight (R w.prev e r) 0
 let g(w:Flap M):= markQ (S.coverQ x u w.next) (R w.next e r-Z w)
 have H:= S.trimmed T R B N G I hu hp he
 have hQ : Carry (flapL M L) (fun w=>s w.volW) fun w=>g w*d w.next:= Carry.charge (Carry.scale (w:=fun w=> d w.next) H) (by
   have h' : Carry (flapL M L) (fun w=> s w.volW) fun w=> s w.volW * ((d w.prev)⁻¹*d w.next):= Carry.mul_right (Carry.unit ..) G.past
   convert h' using 1; ext1 w; exact mul_assoc ..)
 have hE : Carry L s (fun w=> f (Page.opening M w)*d (Page.opening M w)):=by
    convert Carry.scale (w:=fun w=> d (Page.opening M w)) (I.starts e he r hr) using 1;ext1 w;exact (ticket.worth G.root G.limit (s:=s) (Page.opening M w)).symm
 have hV : Carry (coverL M L) (fun w=> s w.bindW) (fun w=>f w*d w):= by
   apply turning _ hQ _ B.depth hE
   intro w; let F:= S.coverQ x u w.next
   let W:= S.yard x u w
   have he': markQ F (Z w)≤markQ W (R w.prev e r)*c w^r:= (S.sight w).upright (S.ridge_pos w) (Premium.rooted (native _ (S.ridge_pos w) u) (x w.volW)) (ne_top_of_le_ne_top ENNReal.one_ne_top (G.fund.cap _)) (S.pole_cost G.fund le_rfl w) _ (ne_top_of_le_ne_top (retained S T R B N G I hu w he) (quota_mono _ (fun z=> W.width_unit z)))
   have hx : markQ F (Z w)*d w.next≤ f w.prev*d w.prev:= by
     calc
      _ ≤ markQ W (R w.prev e r)*c w ^ r *d w.next := mul_le_mul_left he' _
      _ ≤ _:= by
         rw [mul_assoc]; apply mul_le_mul'
         · exact Post.on_fewer (M:=S.camp) S.ridge_pos (l:=S.ridge) S.radius_climb (x:= step_center M x) w _
         exact le_trans (mul_le_mul_left (pow_le_pow_of_le_one (by positivity) (G.fund.cap _) hh) (d w.next)) (G.cool w)
   calc
     _ ≤ (markQ F (Z w)+g w)* d w.next:= by
        apply mul_le_mul_left
        apply le_trans _ (quota_add (Z w) (R w.next e r-Z w) F.width)
        rw [show Z w+_= R w.next e r from add_sub_cancel ..]; exact le_rfl
     _ ≤ _:= by rw [add_mul]; exact add_le_add_left hx _
 refine Carry.mono (Carry.scale (w:=fun w=>(d w)⁻¹) hV) ?_
 intro w; change f w≤ f w*d w*(d w)⁻¹
 rw [mul_assoc,ENNReal.mul_inv_cancel (G.root w) (G.limit w),mul_one]

/-- Positive rank transmission on the cover (with arbitrary forcing). -/
theorem glides : ∀ e ≤ p,∀ r,0<r → Claim (coverL M L) (S.coverQ x u) (ticket d s) (fun w=>R w e r):= by
 apply editions (fun i=>i+m) 1 (P:=fun e r=>Claim (coverL M L) (S.coverQ x u) (ticket d s) (fun w=>R w e r))
 · intro e he r hr _ hv; rcases lt_or_ge r α with h | h
   · have h': ∀ w,R w e r=0:= fun w=> I.sanctity w e r he hr h
     simp_rw [h']; exact Claim.zeroQ
   exact S.finances T R B N G I hu hv he hr h
 intro e he r hr _
 have h w : R w e r=0:=Classical.byContradiction fun h=> not_lt.mpr (I.rank w e he r h) hr
 simp_rw [h];exact Claim.zeroQ
end YM.RegulatorIR.Ledger.Sky
