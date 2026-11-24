import YM.Contacts.Barrage.Slope
namespace YM.Contacts.Barrage.Slope
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent Draw PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{s η:ℝ≥0}{b:ℝ}{P: Patch}{B H:Bed}{m f L : Side}{n k r:ℕ}{S: StepData m f}{R: Spine.voyage S.patch.L}
-- reuse private GaugeJets proof, now with space-address Pad
section
private def Lx (i : Fin 3) : Corn (MapSpec G) →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
    toFun p := WithLp.toLp 2 fun j => p (i,j)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
private def wax (i : Loc G 1) (p : Corn (MapSpec G)) : ℝ :=
    G.plog (G.mat (G.lieExp (Lx 0 p) * G.lieExp (Lx 1 p) * (G.lieExp (Lx 2 p))⁻¹)) i.2
private def unitRead (i : Loc G 1) (p : MapSpec G) : Candles G := if p.1=1 then Sum.inr (i.1,p.2) else Sum.inl (vac,p.2)
private def unitOff (i : Loc G 1) (p : MapSpec G) : Cover := if p.1=2 then step (axisEquiv.symm i.1) else 0
private lemma waxed (i : Co m (Loc G 1)) : (fun x => dragged G m x i)= wax i.2 ∘ consult (MapSpec G) unitRead unitOff ℝ i := by
  funext x; rcases i with ⟨k,a,j⟩
  obtain ⟨i,rfl⟩ := axisEquiv.surjective a; rw [coord_map,← arm_apply G m 1 (dragged G m x) k (coord i) j]
  simp only [dragged, Function.comp_apply]; rw [moveField,content_at]
  unfold wax
  simp only [shiftLinks,Lattice.gauge,encode_link,switchSite]
  let T := consult (MapSpec G) unitRead unitOff ℝ (k,coord i,j) x
  have h1 : arm G m 0 (bundleSites x).1 (k,vac)=Lx 0 T := by ext; simp [T,bundleSites,Lx,unitOff,unitRead,consult,arm_apply]; rfl
  have h2 : arm G m 1 (bundleSites x).2 (k,coord i)=Lx 1 T := by ext; simp [T,bundleSites,Lx,unitOff,unitRead,consult,arm_apply]; rfl
  have h3 : arm G m 0 (bundleSites x).1 (k+step i,vac)=Lx 2 T := by ext; simp [T,bundleSites,Lx,unitOff,unitRead,consult,arm_apply,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _,add_comm (step i)]; rfl
  rw [h1,h2,h3]
private lemma wax_analytic (i : Loc G 1) : AnalyticAt ℝ (wax i) 0 := by
  let K (b : Corn (MapSpec G)) := G.mat (G.lieExp (Lx 0 b) * G.lieExp (Lx 1 b) * (G.lieExp (Lx 2 b))⁻¹)
  have hK : ContDiffAt ℝ ω K 0 := by
    unfold K; simp only [G.mat_mul,G.mat_inv]
    have hk (i : Fin 3) : ContDiffAt ℝ ω (fun b : Corn (MapSpec G) => G.mat (G.lieExp (Lx i b))) 0 := (G.exp_jet.comp (Lx i).contDiff).contDiffAt
    exact ((hk _).mul (hk _)).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hk _))
  have h : ContDiffAt ℝ ω (G.plog ∘ K) 0 := ContDiffAt.comp _ (by simp only [K,map_zero,G.mat_lieExp_zero,mul_one, inv_one, G.mat_one]; exact G.plog_diff) hK
  exact (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i.2).analyticAt _ |>.comp h.analyticAt

private lemma zero_wax (i:Loc G 1): wax i 0=0:= by simp [wax]
def chart (G:Gauge) : Pattern (MapSpec G) (Candles G) (Dye G) := ⟨fun i j=> (unitOff i j,unitRead i j), wax,wax_analytic,zero_wax⟩
lemma fixed (G:Gauge): (chart G).stencil m=dragged G m := by funext x i; rw [show dragged G m x i=_ from congr_fun (waxed i) x]; rfl
end
open Radial Kale Resetter Ion Lumen Convoy Origin
local notation "C" => (chart G)
def stops (n:ℕ):= Finset.univ.erase (OrderedFinpartition.atomic n)
def slew (x:OrderedFinpartition n):ℝ:= (n.factorial:ℝ)⁻¹*x.length.factorial
lemma kin_step (A: Link G m→ℝ)(h:Guards A k)(hx:n<k)(H:Rack (Lines G m 1))(hp:∀ i≤n,Poem (H i))(ht:∀ i≤n,∀ x, jet A i x=design (H i) x) (x: House.Dir (Co m (Candles G))):
    design (H n) (fderiv ℝ (dragged G m) 0 x)= design (H n) (bundleLink x)- ∑ j∈stops n, slew j*design ((C).folded j (H j.length)) x:= by
   have he : Rays k (A ∘ (chart G).stencil m - A ∘ bundleLink) := by
     rw [fixed]; exact merkin (f:=fun z:Swatch G m=> A (moveField z)-A z.2) ((AnalyticAt.comp (f:=moveField) (by rw [moveField_zero]; exact h.analytic) moveField_analytic).sub (h.analytic.comp (f:=Prod.snd (α:=BaseSites G m)) (x:=0) (contDiffAt_snd).analyticAt)) h.grade bundleSites ((bundleSites).analyticAt _) (map_zero _)
   have hA:= h.analytic; have hK:= congr_arg (fun F:House.Dir (Co m (Candles G))→Link G m=> fderiv ℝ F 0 x) (fixed (m:=m) G); have hw:= (nightwalk (AnalyticAt.comp (f:=(chart G).stencil m) (by rw [(C).zero_stencil]; exact hA) (C).analytic) (AnalyticAt.comp (f:=⇑(bundleLink (G:=G) (m:=m))) (by rw [map_zero]; exact hA) ((bundleLink).analyticAt _)) he n hx x); rw [Garf.woven hA, ht _ le_rfl, (C).metro A x _ hA hp ht,mul_sum] at hw; let p (j:OrderedFinpartition n):= (n.factorial:ℝ)⁻¹ * ((j.length.factorial:ℝ)*design ((C).folded j (H j.length)) x); let y:=OrderedFinpartition.atomic n; have hf j:p j=slew j*design ((C).folded j (H j.length)) x:= (mul_assoc ..).symm
   suffices he:p y=design (H n) (fderiv ℝ (dragged G m) 0 x) by rw [← hw, ← he]; simp_rw [← hf]; rw [eq_sub_iff_add_eq]; exact add_sum_erase _ p (mem_univ y)
   unfold p y; rw [(C).atom_form,hK]; exact inv_mul_cancel_left₀ (by positivity : (n.factorial:ℝ)≠0) _
lemma stops_lt (i:ℕ) (p:OrderedFinpartition i)(h:p∈stops i) : p.length < i := lt_of_le_of_ne p.length_le (fun v=> (mem_erase.mp h).1 (Stationary.allSingle p v))
variable {α β:Type}
abbrev terraceP (i:ℕ):Side:= ⟨i+1, by omega⟩
lemma stepping : Tendsto (fun i=>(terraceP i).val) atTop atTop := tendsto_atTop_mono (f:=id) (show ∀ i:ℕ,i≤ (terraceP i).val from Nat.le_succ) tendsto_id
lemma receives [NeZero n][Fintype α]{s η:ℝ≥0}{F X:Field (Fin n) (Node α)} {A B:∀ m,Field (Fin n) (Co m α)} (hp: Rooted (terrain s _) F b) (hq:Rooted (terrain η _) X u) (hg:∀ m,Shadow (lower m) F (A m)∧Poem (A m)∧Shadow (lower m) X (B m)∧Poem (B m)) (hv:∀ m,design (A m)=design (B m)): F=X:= shadow_compare (k:=fun i=>A (terraceP i)) stepping hp hq fun i=> by
   let m:=terraceP i; obtain ⟨h,hX,H,hY⟩:=hg m; have he : A m=B m:= unique_poem hX hY (MvPolynomial.funext fun u=> congr_fun (hv _) u); exact ⟨h,he.symm ▸ H⟩
def shipped (s:ℝ≥0)(L:Side)(α β:Type)[Fintype α][Fintype β] (i:ℕ)(b:ℝ) := (Fintype.card (Co L α):ℝ)*beamPrice s b*(Fintype.card β * beamPrice s b)^(i-1)
abbrev lifts (P:Cross L α β) (F:Field (Fin r) (Node α)):= hoist (install P) F
lemma roof_lift [Fintype α][Fintype β]{W:Cross L α β}{X:Field (Fin n) (Node α)} (hp: Rooted (terrain s _) X x)(hb:0≤b) (hw:W.strip η b)(hx:(η:ℝ)/L.val ≤ (s:ℝ)) : Rooted (terrain η _) (lifts W X) (x * shipped η L α β n b) := by
    convert hoist_pay (influx hx) (ledgers hw hb) hp using 1 <;> try rfl
    unfold shipped; ring
def lottery (n:ℕ)(G:Gauge)(A:Rack (Node (Dye G))):= ∑ i∈stops n,slew i • ((chart G).blend i (A i.length))
def drops (T:ℝ≥0)(n:ℕ)(G:Gauge)(A:ℕ→ℝ):= ∑ i∈stops n, ‖slew i‖ * ((∑ u ,(chart G).shelfFee i T u)* A i.length)
lemma lottery_due {z:Rack (Node (Dye G))}{h:ℕ→ℝ}{t:ℝ≥0} (he:s≤t)(hp:∀ i < n, Rooted (terrain s _) (z i) (h i)) : Rooted (terrain s _) (lottery n G z) (drops t n G h):= Rooted.aggregate _ fun i hi=> ((chart G).blend_price i he (hp _ (stops_lt n i hi))).smul _
-- need bind Q Think Witness (Awake). mapProof for any rank k.
variable {V:bore G}{Q:KernelChoices}{T:Stairs G P.L}{A:Spine.voyage P.L}{X:ℕ→ℝ}
-- estimate uses nonempty p≥1; sum ranks≤n price
include B H Q
lemma carpet {t d:ℝ≥0} [NeZero n] (hh : (η:ℝ)/P.L.val≤s)(h:s≤d)(ht:Awake G P Q B H A v)(hq:Cabinet (brick G P Q.penalty B) T)(hT:T.strip η x)(hx:0≤x)(hw:A.strip t b)(hw':η≤t)(hb:0≤b)(hu:(Origin.stretch P Q G T).strip η u)(hu':0≤u)(hF: Light V)(hl:∀ i≤ n,Rooted (terrain s _) (dazzle V k i) (X i)): let Z:=dazzle V k; let A':= Origin.bleed G A; let Q':= Origin.stretch P Q G T; lifts Q' (Z n) = lifts A' (Z n)- lifts (nest P G A) (lottery n G Z) := by
   intro Z A' Q'; let ζ:=Candles G; let R:=lifts (nest P G A) (r:=n); have HM:= lottery_due h (fun i hi=> hl i hi.le)
   let U(m:Side):=sprig P Q m; let f(m:Side): Side:= m*P.L; let V' (m:Side)(i:ℕ):=dazzle (hair V (f m)) k i; let L(m:Side): Field (Fin n) (Co (f m) (Candles G)):= ∑ i∈ stops n,slew i • (C).folded i (V' m i.length)
   let a (m:Side):= hoist (installed (U m).ratio A') (V' m n); let y (m:Side):= hoist (installed (U m).ratio Q') (V' m n); let c (m:Side):=hoist (installed (U m).ratio (nest P G A)) (L m); have ha:= bleed_strip (G:=G) (strip_mono hw (NNReal.coe_le_coe.mpr hw') le_rfl) hb; let H' (m:Side) (i:ℕ):Poem (V' m i):= by unfold V' dazzle; split; apply (cradle_shape hF.my).poem; apply Poem.empty
   have hk (m:Side) i: Shadow (lower (f m)) (Z i) (V' m i):= by unfold Z V' dazzle; split; apply printFeeds (heritage (fun i=>hF.my.here i _ _) (f m)); apply Shadow.empty
   have hm := hl n le_rfl; let HE:= succeeds (G:=G) hw hw' hb; have HU:0 ≤ spanned P t b:= spanned_positive hb
   refine receives (A:=y) (B:=fun m=>a m-c m) (roof_lift hm hu' hu hh) ((roof_lift hm hb ha hh).sub (roof_lift HM HU HE hh)) (fun m=> ?_) (fun m=>?_ )
   · let T' := (U m).ratio; refine ⟨hoist_period (influx hh) (ledgers hu hu') hm (hk m n) (st_new T' Q'), hoist_shape, ?_,?_⟩
     · have hx: Shadow (lower (f m)) (lottery n G Z) (L m):= Shadow.aggregate _ _ (fun i _=> ((C).blend_price i le_rfl (hl i.length (i.length_le))).smul (slew i)) (fun i _=> ((C).blend_shadow i (hl i.length i.length_le) (hk m i.length)).scale (slew i))
       simp_rw [sub_eq_add_neg]; have he:= hoist_period (influx hh) (ledgers HE HU) HM hx (st_new T' (nest P G A)); refine (Shadow.add (hoist_period (influx hh) (ledgers ha hb) hm (hk m n) (st_new T' A')) (show Shadow _ (-lifts (nest P G A) (lottery n G Z)) (-c m) from ?_) (roof_lift hm hb ha hh) ((roof_lift HM HU HE hh).neg)); exact (by simpa only [neg_one_smul] using he.scale (-1:ℝ))
     rw [sub_eq_add_neg]; exact hoist_shape.add (Poem.minus hoist_shape)
   · let g:= (U m).ratio; let T':= (installed g (nest P G A)); let w:= wind (hair V (f m)) (n+k+3) k; have hw': Guards w _:= hF.protects (n+k) (f m) k (by omega); have ht':= ht.primary m;
     funext X'; let b:= installed (U m).ratio Q' *ᵥ X'; let Y:=installed g A' *ᵥ X'; let v:=T' *ᵥ X'; have h₁ : b=fderiv ℝ (dragged G (f m)) 0 v:=(congr_arg (fun L=>L*ᵥ X') (rise_roll (S:=U m) T ht.sign_f hq hT hx ht')).trans (forestDrag (S:=U m) (G:=G) X' hw).symm
     have hp : ∀ i≤n,∀ t, jet w i t= design (V' m i) t:= fun i hi t=>by unfold V'; rw [glitter]; exact (wind_jet ..).trans (if_pos (by omega))
     rw [parcel_sub]; rw [show design (a m) X'=_ from (show _= design (V' m n) Y from hoist_read _ _ _), show design (y m) X'=_ from (show _= design (V' m n) b from hoist_read _ _ _),show design (c m) X'=_ from (show _ = design (L m) v from hoist_read _ _ _)]; rw [h₁,kin_step w hw' (by omega) (V' m) (fun i _=> H' m i) hp,show bundleLink v=Y from link_nest X']; congr 1; unfold L design; rw [verse_sum, map_sum]; simp only [verse_scale',map_smul]; rfl
end
end YM.Contacts.Barrage.Slope
