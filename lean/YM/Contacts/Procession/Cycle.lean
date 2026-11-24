import YM.Contacts.Procession.Pleats
import YM.Planned.PRIMARY_INTEGRAL_295.Edens
/-! The polynomial-keeping canonical harmonic filter applies in every period of the analytic step. Can use truths on this representative via Slope & Health. No alterations to Rep.history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Pierian
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales Port
open Planned.PrimaryIntegral295 Carrier
variable {G:Gauge}{n k i r l p j:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
-- all statements use the P from Actor, not stamping plot
abbrev park (i n:ℕ) := destination e.a n i
abbrev total (i n:ℕ): AtomBeam (e.R i) := linesOf (park e i n) e.a.clock.kernel.penalty
lemma awakeV (h:i<n): let R:= e.R i; Awake G R e.a.clock.kernel (e.M.H n (i+1)) (e.M.H n i) (total e i n) (e.T.η (e.J (i+1))) := by
    intro R; let W:= awakened e.lamp h; let A m:= e.a.clock.op i m; let K:=e.a.clock.kernel; let X:= total e i n; have hx: Whole X:= Carrier.stored _ K.penalty K.penalty_pos (e.a.clock.adm i); refine ⟨W.alive,W.sign_f,W.sign_c,W.gap,W.edge,W.handy,fun m=>?_ ⟩; let S:= sprig (e.R i) K m; apply (projected_ray (sprig (e.R i) K m) W.sign_f W.sign_c X hx).2
    -- already true curvature/roll on e-meshes.G Σ Tape.H
    have H v := (Edens.laureates e.a e.M e.lamp n i v h).2.1.trial
    obtain ⟨h₁,h₂⟩:= breeze (M:=X) (K:=K) W.sign_f W.sign_c hx (side_diverges e.a.S i) (Eventually.of_forall (fun m=>((projected_ray (e.a.clock.op i m) W.sign_f W.sign_c X hx).1 (H m)))); exact ⟨congr_arg (fun Q=>Row.acts Q m) h₁,congr_arg (fun Q=>Row.acts Q m) h₂⟩
structure Charter (b:ℝ) (T:MapPrices): Prop where
   wealth j (m:ℕ) (h:4 ≤ j) (he:4 ≤ m) (hp:m ≤ j) (P:Flight j m) (l:List Axis): l.length ≤ j-2 → (advanceC P.L (linesOf P b) l).strip (T.α j) (purse T j/(P.L.val:ℝ)^(1+l.length))
private lemma stage_pay (x:0<b) (i j:ℕ): ∃ σ C:ℝ,0<σ ∧ 0<C ∧ ∀(P:Flight j i)(l:List Axis), 4 ≤ i → 4 ≤ j→l.length ≤ j-2→ (advanceC P.L (linesOf P b) l).strip σ (C/(P.L.val:ℝ)^(1+l.length)):= by
   by_cases h: 4 ≤ i ∧ 4≤j; swap; · exact ⟨1,1,zero_lt_one,zero_lt_one,fun _ _ h' hi=> False.elim (by omega)⟩
   obtain ⟨σ,C,hσ,hC,h⟩:=Carrier.priced b x h.2 h.1; exact ⟨σ,C,hσ,hC,fun P l _ _=> h P l⟩
lemma taxes (x:0<b):∃ T:MapPrices, Charter b T:= by
    choose s C hs hC h using stage_pay x; let σ (j:ℕ) := min (s j j) (s (j-1) j); let c (j:ℕ):= max (C j j) (C (j-1) j); let T:MapPrices:= ⟨σ,c,fun _=>1,fun i=>lt_min (hs i i) (hs _ i),fun _=>zero_lt_one⟩; refine ⟨T,⟨fun j m hj hm hp P l hL=>?_⟩⟩; have he:= P.narrow; have hh : m=j ∨ m=j-1 := (by omega); apply strip_mono (h m j P l hm hj hL); · rcases hh with h|h; rw [h]; apply min_le_left; rw [h]; apply min_le_right
    refine div_le_div_of_nonneg_right ?_ (by positivity); rcases hh with h|h; exact h.symm ▸ ((le_max_left _ _).trans (le_max_right 1 (c j))); exact h.symm ▸ ((le_max_right _ _).trans (le_max_right 1 (c j)))
-- book canonical prices (m = actual earlier stage); pay covers all postL constants here incl moments needed for further Boost; nothing actually asked about prepare field below.
abbrev portal (b:ℝ)(h:0<b):= (taxes h).choose
structure Sponsored (T:MapPrices)(j:ℕ) (P:Patch) (y:ℝ):Prop where
    width : 2*narrow y ≤ rentCheque T j
    span : spanned P (rentCheque T j) (purse T j) ≤ lush y
lemma after_caps (P:Patch)(T:MapPrices)(j:ℕ) : ∀ᶠ y in atTop,Sponsored T j P y:= by
    let t:= rentCheque T j; have ht:= NNReal.coe_pos.mpr (rent_pos T j); filter_upwards [lush_matures.eventually_ge_atTop (spanned P t (purse T j)), lush_matures.eventually_ge_atTop (2/(t:ℝ))] with y he hy; refine ⟨?_ ,he⟩; apply NNReal.coe_le_coe.mp; push_cast; change 2*(lush y)⁻¹ ≤ (t:ℝ); rw [← div_eq_mul_inv,div_le_iff₀ (lush_pos y)]; exact ((div_le_iff₀ ht).1 hy).trans (mul_comm ..).le
private def due (T:MapPrices)(j:ℕ)(L:Side):ℝ:= if h:∃ P:Patch,P.L=L ∧ P.J=j then (eventually_atTop.mp (after_caps h.choose T j)).choose else 0
lemma sufficient (L:Side)(T:MapPrices)(P:Patch)(h:P.L=L ∧ P.J=j) (x:ℝ)(hp:due T j L≤x): Sponsored T j P x:= by
   let w:∃ P:Patch,P.L=L∧P.J=j:=⟨P,h⟩; rw [due,dif_pos w] at hp; have ht:P=w.choose:= by exact (fun (q : Patch) (hh:q.L=L ∧ q.J=j)=>by apply (show ∀ (P Q:Patch), P.J=Q.J→P.L=Q.L→P=Q from by rintro ⟨L,i,_⟩ ⟨p,q,_⟩ h h'; cases h; cases h'; rfl) P q (h.2.trans hh.2.symm) (h.1.trans hh.1.symm) : ∀ q:Patch,(q.L=L∧q.J=j) → P=q) w.choose w.choose_spec
   rw [ht]; exact (eventually_atTop.mp (after_caps w.choose T j)).choose_spec x hp
open Org PhysicalNext.Repeat.Legato
-- heft.Rival applies to TRUE clock-grade (same Quote as Comet). Received allowance for Canon orientation.
def wineBid (t:BidTri G)(T:MapPrices)(P:Rival): BidTri G:= ⟨fun K i=>max (t.w K i) (Port.charge G T i (P.ups K i)),fun U p i=> max (t.pay U p i) (due T i (p i))⟩
structure Led (R:Rival)(e:Oasis G)(P:MapPrices): Prop where
    wealth i : Sponsored P (e.J (i+1)) (e.R i) (e.a.clock.hatBeta i)
    outer i : Port.charge G P (e.J (i+1)) (R.ups e.T (e.J (i+1))) ≤ (e.L i).val
lemma bonus (t:BidTri G)(P:Rival)(T:MapPrices)(u:Passage G)(h: admits (wineBid t T P) u): admits t u ∧ ∀ i,let j:=u.A.B.a.clock.J (i+1); Port.charge G T j (P.ups u.M.K j) ≤ (mainFlag u.A.B.a i).L.val ∧ Sponsored T j (mainFlag u.A.B.a i) (u.A.B.a.clock.hatBeta i):= by
    refine ⟨fun i=>⟨(le_max_left ..).trans (h i).1,(le_max_left ..).trans (h i).2⟩,fun i=> ⟨(le_max_right ..).trans (h i).1,?_⟩⟩;
    refine sufficient (u.L.L (u.A.B.a.clock.J (i+1))) T (mainFlag u.A.B.a i) (j:=u.A.B.a.clock.J (i+1)) ⟨(u.A.B.a.fits.sameFactor i).symm.trans (congr_fun u.A.B.valid.lengths _),rfl⟩ _ ((le_max_right ..).trans (h i).2)
end YM.Contacts.Procession.Pierian
