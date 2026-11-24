import YM.OPE.Compatible.Basil.Simple
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mean
/-!
# μ on globally tiny W. Saddle error separately from μ size, topology only locally needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census
open Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (M:Leaf S R)
lemma vacantX (hc:RG.flags (Pressure.temp X.x) X.V=∅) (hw: troupe T R Q.halo X.B p) (hh:Cash.numP p=0):
   (planted X p).seeds.place=∅:=by
   have hp : p.toLeft=∅ :=Finset.eq_empty_iff_forall_notMem.mpr fun j hj=>by
     have h:= hw.1.checkpoints _ hj
     have h':0 < j.shares := shares_nonzero S _ _ h
     exact Nat.ne_of_gt (lt_of_lt_of_le (show 0 < Mixed.shares S (.inl j:Head S) from h') (single_le_sum (f:=Mixed.shares S) (fun _ _=>Nat.zero_le _) (mem_toLeft.mp hj))) hh
   unfold planted preps; dsimp only; rw [hc,place]; dsimp only; unfold roster; rw [hp]; simp only [Finset.biUnion_empty]; simp [Packets.store]; constructor <;> ext <;> simp
lemma vanished (h:X.seeds.place=∅)(i:Site c)(l:ℕ):¬Inside i X.seeds l:=by
   unfold Inside dome; simp [h,halo_spec]
lemma outboard (h:X.seeds.place=∅)(i:Bond f)(hF:i∉F.trunks) : X.Hot i := far_active X.seeds F i (vanished X h _ _) hF
lemma driftLens (h:X.seeds.place=∅)(k Q₀ r α E w:ℝ)(L:Side) (hR:Rotator P L k r Q₀ α X)
    (v: Directions G f) (hs:‖v‖≤w)(ht:0≤E)(hn:∀ i∈F.trunks,v i=0)
    (hp:∀ i:Mention c f, ‖X.realPath i.1 i.2 v‖≤E) :
    let m:=tubularPrice G L
    ∀ i:Bond f, ‖X.μ i‖ ≤ (Fintype.card G.ColorIndex:ℝ)*(payE k r Q₀ m * (α*(scale*E)) + scraps k r Q₀ m X.B * w + w):=by
   intro m i; let hgb:= α*(scale*E); have hg : 0≤ hgb:=mul_nonneg hR.signs.le (mul_nonneg scale_pos.le ht)
   let Y:= payE k r Q₀ m * hgb+ scraps k r Q₀ m X.B*w; have hb : 0≤w:= (norm_nonneg _).trans hs
   have hZ:0≤Y:=add_nonneg (mul_nonneg hR.scale.disc hg) (mul_nonneg (hR.scale.heap _) hb)
   refine color_cover (add_nonneg hZ hb) _ fun j=> ?_
   let t:Tubular f G:=(i,j)
   have hp' : |X.driftM t - stand v t| ≤ Y:= X.drift_point v t hs hR hg (fun j _=>X.coil v E hn j (vanished X h _ _) hR ht fun i _=> hp i)
   have hf:|stand v t|≤ w:= le_trans (stand_cap ..) ((norm_le_pi_norm v i).trans hs)
   change |X.driftM t| ≤ Y+w
   apply le_trans (b:=|X.driftM t-stand v t|+ |stand v t|) ?_ (add_le_add hp' hf)
   simpa only [sub_add_cancel] using abs_add_le (X.driftM t- stand v t) (stand v t)
lemma boundLens (P:Teller G)(L:Side)(D:Patch)(hd:D.Branches P.bind G){u:ℝ→ℝ}(hw:Rate G L (-(1/2)) u) (hh:∀ᶠ x in atTop,0≤ u x)(η r Q Y : ℝ)(hi:Torch η r Q) :
   ∃ c z,0≤c∧Rate G L (-1) z∧ ∀ᶠ x in atTop,0≤ z x ∧ ∀ (c' f:Side) (S:StepData c' f)(T:Tube G S), S.patch=D → S.patch.L=L → Room P S T x → Stamp T → ∀ (F:Forest S.ratio)(X:Coat T F) (b:LogField G c'),
     Rotator P L η r Q Y X→ X.x=x → X.manifest → X.seeds.place=∅ → X.V=represent b → ‖b‖≤ u x → ∀ (i:Bond f), ‖X.μ i‖≤c * u x + z x:=by
   obtain ⟨Z,hZ,H⟩:= retreat P L D hd hw hh; obtain ⟨C,hC,H'⟩:= spring_cap P
   let W(x:ℝ):= C*u x; let m:= tubularPrice G L; let U(x):= (payE η r Q m * (Y*(scale*Z x))) + scraps η r Q m (radiusB x)* W x
   let c:ℝ:=Fintype.card G.ColorIndex
   have he : Rate G L (-1) U := by
      refine Rate.add (((hZ.mul_left _).mul_left _).mul_left _) ?_
      convert (hi.physical G L (-(1/2)) m).mul (hw.mul_left C) using 1; norm_num
   have ha: Rate G L (-1) (fun x=> |c*U x|):=(he.mul_left c).compare (Eventually.of_forall fun x=>(abs_abs _).le)
   refine ⟨c*C,_,mul_nonneg (by unfold c; positivity) hC.le,ha,?_⟩
   filter_upwards [H] with x hx
   obtain ⟨hV,hT⟩:=hx; refine ⟨abs_nonneg _,?_⟩; intro l f S T hS hL hR h F X b H₀ hx he' ht hb hw i; subst x
   let z:Site l→G.El:=1; let v:= X.radiate z b
   have hv : ‖v‖ ≤ W X.x:=(spin_bounded ..).trans ((H' S T hR.accepted F b).trans (mul_le_mul_of_nonneg_left hw hC.le))
   have hf:=driftLens X ht _ Q _ _ _ _ L H₀ v hv hV (X.trench z b) fun (i:Mention l f)=> hT l f S T hS hL hR h F X rfl he' i z b (vanished X ht _ _) (fun j _=> by simp [Lattice.gauge,z,hb]) hw
   have hh' : c*C*u X.x=c*W X.x:=mul_assoc ..
   apply (hf i).trans; change c*(U X.x + W X.x)≤ _; rw [mul_add, add_comm _ (c*W X.x),hh']; exact add_le_add_right (le_abs_self _) _
end YM.PhysicalNext.Repeat.Aroma
