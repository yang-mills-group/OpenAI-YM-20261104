import YM.Contacts.Milling.Convoy
import YM.Contacts.Pulse.Epoch
/-! Beam issue from true Horizon comparison. `Passport` conservation proof on all test periods. -/
noncomputable section
namespace YM.Contacts.Milling.Lumen
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent
open scoped Topology BigOperators Classical Matrix NNReal ContDiff
variable {α X W:Type}
variable {B H : Bed}{A S:Patch}{K:KernelChoices}{G:Gauge}{c f:Side}{k:ℕ}
abbrev AtomBeam (P:Patch):= Spine.voyage P.L
section
variable {P:Patch}{M:AtomBeam P}
lemma projected_ray (A:StepData c f)(hf:Whole B.metric)(hh: Whole H.metric)(U:AtomBeam A.patch)(hw:Whole U) : let S:=connectorRow A.patch
      let k:= A.kernel.penalty
      Inputs A (installed A.ratio U) (B.metric.acts f) (H.metric.acts c) ↔ (composeRows (reblock A.patch.L (krow B.metric)) U).acts c=(composeRows (transRows S) (krow H.metric)).acts c ∧ (composeRows S U).acts c=(minusRows (unitRow (TypeFace 1)) (scaleRows k⁻¹ (krow H.metric))).acts c:= by
   intro S k; have hs : Whole S := by obtain ⟨x,hX,h⟩:= ready_connectorRow A.patch 1; exact ⟨_,_,zero_lt_one,h⟩
   let T:= A.ratio; let e:= splitCo T (TypeFace 1); have hu:= k_capacity hf; have hv:= k_capacity hh
   have ht: Precision.K (B.metric.acts f)=(reblock A.patch.L (krow B.metric)|>.acts c).submatrix e e:= by rw [← Krow_acts _ hf]; obtain ⟨s,k,hs,h⟩:=hu; exact reblock_periods T hs.le h
   let N:= composeRows (reblock A.patch.L (krow B.metric)) U; let V:=composeRows (transRows S) (krow H.metric)
   have hg: Precision.K (B.metric.acts f)*installed A.ratio U=(N.acts c).submatrix e id:= by rw [ht]; unfold N; rw [(reblock_all hu).acts hw]; apply Matrix.submatrix_mul_equiv
   have hx: (mean A)ᵀ * Precision.K (H.metric.acts c)=(V.acts c).submatrix e id:= by rw [block_mean,Matrix.transpose_submatrix]; unfold V; rw [hs.flipped.acts hv,acts_trans]; rw [show (krow H.metric).acts c=_ from Krow_acts _ hh c]; exact Matrix.submatrix_mul_equiv (S.acts c)ᵀ (Precision.K (H.metric.acts c)) e (Equiv.refl _) id
   have hl: mean A * installed A.ratio U=(composeRows S U).acts c:= by rw [hs.acts hw,block_mean,installed]; erw [Matrix.submatrix_mul_equiv _ _ (id) e (id)]; rfl
   have hr: 1-A.kernel.penalty⁻¹ • Precision.K (H.metric.acts c)=(minusRows (unitRow _) (scaleRows k⁻¹ (krow H.metric))).acts c:= by erw [(Whole.coin _).less (hv.weight _),acts_unit,acts_scale,Krow_acts _ hh]
   constructor
   · intro h; obtain ⟨h₁,h₂⟩:=h; rw [hg,hx] at h₁; refine ⟨?_,hl ▸ hr ▸ h₂⟩; ext i j; obtain ⟨i,rfl⟩:=e.surjective i; exact congr_fun (congr_fun h₁ i) j
   rintro ⟨h,h'⟩; exact ⟨hg.trans <| Eq.trans (congr_arg (fun (Q:Matrix _ _ ℝ)=>Q.submatrix (e:_→_) id) h) hx.symm,hl.trans (h'.trans hr.symm)⟩
end
variable {P:Patch}{M:AtomBeam P}{a b d u e:ℝ}{t:StepData c f}{X:ℕ→Side}{n:Side}
lemma breeze (hf:Whole B.metric)(hh:Whole H.metric)(hw: Whole M) (hx:Tendsto (fun i=>(X i).val) atTop atTop) (he:∀ᶠ i in atTop,(composeRows (reblock P.L (krow B.metric)) M).acts (X i)=(composeRows (transRows (connectorRow P)) (krow H.metric)).acts (X i) ∧ (composeRows (connectorRow P) M).acts (X i)=(minusRows (unitRow (TypeFace 1)) (scaleRows K.penalty⁻¹ (krow H.metric))).acts (X i)) :
     composeRows (reblock P.L (krow B.metric)) M=composeRows (transRows (connectorRow P)) (krow H.metric) ∧ composeRows (connectorRow P) M=minusRows (unitRow _) (scaleRows K.penalty⁻¹ (krow H.metric)) := by
   have glue {α X':Type}{A B: Row α X'}(hp:Whole A)(hu:Whole B)(hg:∀ᶠ i in atTop,A.acts (X i)=B.acts (X i)): A=B := funext fun i=> funext fun j=>funext fun a=> tendsto_nhds_unique (entry_limit X hx A hp.safe i j a) ((entry_limit X hx B hu.safe i j a).congr' (hg.mono fun _ h=> Eq.symm (congr_fun (congr_fun h _) _)))
   obtain ⟨c,a,h⟩:= ready_connectorRow P 1; have h : Whole (connectorRow P):= ⟨_,_,one_pos,h⟩; exact ⟨glue ((reblock_all (k_capacity hf)).prod hw) (h.flipped.prod (k_capacity hh)) (he.mono fun _=> And.left),glue (h.prod hw) ((Whole.coin _).minus ((k_capacity hh).weight _)) (he.mono fun _=> And.right)⟩
-- choose permit all m. shape `stagePoint A.clock m`.
structure Awake (G:Gauge)(P:Patch)(K:KernelChoices)(B H:Bed) (W:AtomBeam P)(s:ℝ): Prop where
   alive : P.Branches K G
   sign_f : Whole B.metric
   sign_c : Whole H.metric
   gap n : Gap (B.metric.acts n) s
   edge : 0<s
   handy n: (B.metric.acts n)ᵀ=B.metric.acts n
   primary n: let S:=sprig P K n; Inputs S (installed S.ratio W) (B.metric.acts (n*P.L)) (H.metric.acts n)
variable {L:Levels G}{N:Horizon L}{T:MapPrices}
abbrev mainFlag (L:Levels G)(i:ℕ):= (L.clock.op i 0).patch
lemma awakened (h:N.Suffices T) {i j:ℕ}(he:i<j): Awake G (mainFlag L i) L.clock.kernel (N.H j (i+1)) (N.H j i) (N.towers j i).A0 (T.η (L.clock.J (i+1))):= by
   let κ:= L.clock.kernel; let v:ℝ:= T.η (L.clock.J (i+1)); let W:= mainFlag L i; let X m:= L.S.side i m; let B:=N.H j (i+1); let H:=N.H j i; let M:AtomBeam W:= (N.towers j i).A0; have hl m:= (h.all j (i+1) he m); have ha:= released h he; have hp:= released h he.le; have hw: Whole M:=⟨_,_,T.alpha_pos _,( (h.costs j i he).2.2.2 [] (by simp)).1⟩
   refine ⟨(L.blocks i 0).branches,ha,hp,fun m=> ⟨fun x=> ((hl m).uniform.1 _).1⟩,T.eta_pos _,fun m=> (hl m).symmetric.1, fun m=>?_⟩; let p:= sprig W κ m; let K:=L.clock.kernel; let Z := K.penalty; apply (projected_ray p ha hp M hw).2; obtain ⟨h₁,h₂⟩:= breeze (M:=M) (K:=K) ha hp hw (side_diverges L.S i) (Eventually.of_forall fun m=> ((projected_ray (L.clock.op i m) ha hp M hw).1 (h.crossings j i m he).trial)); exact ⟨congr_arg (fun Q=>Row.acts Q m) h₁,congr_arg (fun Q=>Row.acts Q m) h₂⟩
structure Blazing (X: bore G)(H: Bed): Prop where
   frame : Cradle (Dye G) X
   pri n: Chest (hair X n) H.metric
   beams (n:Side)(k:ℕ): sealed (hair X n) (k+3)
local notation "Ν" => terrain
private def team (m:Side)(i:ℕ): Side:= ⟨m.val*(i+1),by positivity⟩
private lemma team_dvd (m:Side)(i:ℕ) : m.val∣(team m i).val:= dvd_mul_right ..
private lemma team_h (m:Side) : Tendsto (fun i=>(team m i).val) atTop atTop := tendsto_atTop_mono (f:=id) (fun i=> (show i≤(team m i).val from (Nat.le_succ i|>.trans <| Nat.le_mul_of_pos_left _ m.property))) tendsto_id
variable (σ η:ℝ≥0){X:bore G}{B H:Bed}{M: AtomBeam P}(Q:ChartRatio G) (W:Stairs G P.L){F:TableFee}{Fee:TableFee}
section
variable (hm:Blazing X B)(g:Awake G P K B H M a)(hW: Cabinet (brick G P K.penalty B) W)(hp:Roof η X F) (he:(σ:ℝ)/(P.L.val:ℝ)≤η)
variable (hc: W.strip (σ:ℝ) b)(hq:Row.strip (axisSky G P (Origin.stretch P K G W)) (σ:ℝ) d) (hb:0≤b)(hd:0≤d)(hv: (krow H.metric).strip (2*(σ:ℝ)) u)(hu:0≤u)
include hm g hW hp he hc hq hb hd hv hu
lemma rinknow (i r:ℕ)(hr:r≠0)(n:Side): let S:= sprig P K n; Pulse.Two (voyageW n σ _) (caravan Q P K X W H.metric i r) (Forge.vault S Q (hair X (n*P.L)) (installed S.ratio M) B.metric H.metric i r) (Fare.boot Q P K σ F d b u i r) (hush σ n * Fare.turns Q P K σ F d b i r):= by
   intro S; exact tell (t:=S) σ M W Q (hair X (n*P.L)) hm.frame g.sign_f g.sign_c hW (g.primary n) he hp (fun i r=> printFeeds (n:=n*P.L) (heritage (fun j=> hm.frame.here j i r) _)) hc hb hq hd hv hu i r hr
-- charges only in positive rank, can quote *0* when r=0 on cover
lemma upperroof : Roof σ (caravan Q P K X W H.metric) (fun i r=> if r=0 then 0 else Fare.boot Q P K σ F d b u i r) := ⟨fun i r=> by
   split
   next h=> subst r; rw [(caravan_flow Q P K hm.frame W H.metric).scalar]; exact Pulse.Rooted.tranquility _
   next h=> exact (rinknow σ η Q W hm g hW hp he hc hq hb hd hv hu _ _ h 1).ground⟩
lemma restrung (hs:0<σ)(hQ:LocalRatio Q): Blazing (caravan Q P K X W H.metric) H:= by
   let Y:= caravan Q P K X W H.metric; have hy:= caravan_flow Q P K hm.frame W H.metric; refine ⟨hy,fun n=> carav_roll P K W n hm.frame H.metric g.sign_c,fun n k=>?_⟩
   let A:= team n; let B_f i:= sprig P K (A i); let F' i:= Forge.vault (B_f i) Q (hair X (A i*P.L)) (installed (B_f i).ratio M) B.metric H.metric
   apply Convoy.saved (X:=Y) (k:=k+3) (P:=F') (Fee:=Fare.turns Q P K σ F d b) (team_dvd n) hy (upperroof σ η Q W hm g hW hp he hc hq hb hd hv hu) (fun i=> hush σ (A i))
   · exact tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp (team_h n)).const_mul_atTop (NNReal.coe_pos.mpr hs)))
   · intro i r hr; refine Eventually.of_forall (fun j=> ?_); obtain ⟨Z,hZ,hp⟩:= (rinknow σ η Q W hm g hW hp he hc hq hb hd hv hu i r hr (A j)).owes; haveI : NeZero r:= ⟨hr⟩; rw [focused hZ (lower_onto (A j)) (G:=_) (printFeeds (heritage (fun a=> hy.here a i r) _))] at hp; exact hp
   have he : ∀ᶠ i in atTop, Larger (G:=G) (B_f i) := by
     filter_upwards [(team_h n).eventually (eventually_ge_atTop (100*Pressure.macroR P+3))] with i hi; refine ⟨g.alive,?_ ,?_⟩; · change 100 * Pressure.macroR P≤(team n i).val*P.L.val; exact le_trans (b:=(team n i).val) (by omega) (Nat.le_mul_of_pos_right _ P.L.property)
     change _ ≤ (team n i).val; omega
   exact he.mono fun i hi=> passport (S:=B_f i) hQ (hm.beams _ _) (hm.pri _) ⟨hi,g.edge,g.gap _,g.handy _,g.primary _⟩
end
end YM.Contacts.Milling.Lumen
