import YM.LocalTaylorR2.Exponent.Scull
import YM.LocalTaylorR2.Kiln.Season

/-!
 # Unmask ALL retained inherited path kernels (but only those light inside the appropriate distance & bright at their own anchors). At dark anchors keep as-is: no false estimates from footprint length when there are shared marks. Physical mean and flags tracked.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Canvas Axial Kiln Work.G05
variable {i:Trans f}{X:Coat T F}{K:ℕ→Atom G p}
-- profile & threshold erasement simultanously, all modes
lemma plaza_chapter {O J:Support c}{a:Bond f}(h:a∈ X.plaza O)(hh:∀ z∈O,Cleanroom J 1 z): atEdge S a∈ J:= by
 obtain ⟨x,hx,hy⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp h).2.2; exact hh x hx _ (stride a hy)
set_option maxHeartbeats 600000 in
private lemma footing (v: Site f)(h:v∈(K i.2.2).footprint i.2.1)(hp:light X K i)(p: Room P S T X.x) : separation (axis S i) (S.ratio.parent (affine i.1 0 v)) ≤ X.B:= by
  rw [axis,affine0,S.ratio.parent_signed S.patch.odd_side,separation_signed]; rw [Paths.atom_foot] at h; have he:= (show separation i.2.1 v≤(K i.2.2).length from Paths.where_slot _ _ v h); unfold Kiln.light till at hp; unfold Coat.B; have hy:=Work.E04.parent_separation S.ratio i.2.1 v; have hz:= p.frame; omega
lemma bastion (i:Trans f){z : Air f G}{U:Support c}
    (hm:Cash W X.x μ L Q o C T R) (hM:X.manifest)(hw:X.width=o.K)(hf:light X K i)(hx:¬ dim X i)
    (hp:atomFoot S.ratio Q.halo X.B K i⊆U) (hz:z∉ eerie X U (o.ξ/2) R.beta) (hT:Stamp T) : Healthy R.p.threshold ((K i.2.2).footprint i.2.1) (pull i.1 0 (X.input (worldZ X R.beta z))):=by
   let Z:=X.input (X.liftA R.beta z); have h:=hm.laws.data; let t:= axis S i; have ht:0<X.t:=h.room.fiery; have hF:100≤X.B:=h.room.sight.1
   rw [← shine X h.room hM]; apply Finset.disjoint_left.mpr; intro v hv hV
   have hh: affine i.1 (0:Site f) v ∈ flags R.p.threshold Z:=by rw [← Work.H03.flags_send i.1 _ R.p.threshold Z]; exact mem_image_of_mem _ hV
   have he := footing v hv hf h.room; obtain ⟨x,hA,hC⟩:= (flags_spec ..).1 hh
   have hy : separation t (S.ratio.parent x.1) ≤ X.B+10 := (separation_triangle _ _ _).trans (add_le_add he (show separation _ (S.ratio.parent x.1) ≤10 from (Work.E04.parent_separation S.ratio _ _).trans (by rw [separation_comm]; have hh := Work.E01.sep_touched x _ hA; omega)))
   let y:= S.ratio.parent x.1; have hy':y∈ U:= (pastturn (X:=X) hp (show t∈ homeFoot X K i from heart)) _ (hy.trans (le_trans (b:=500*X.B) (by omega) (Nat.mul_le_mul_right X.B (by exact Q.buys))))
   have h' : X.watch y o.ξ R.beta X.B z := by
     intro p hp; apply (atHome _ _ _ _ _ hz _ hy' p (hp.trans (by omega))).trans
     have hβ:0<gStep R.beta := inv_pos.mpr (Real.sqrt_pos.mpr hm.laws.intake.positive); have he:=o.rare; gcongr; linarith
   have hq : ¬ Inside y X.seeds (30*X.B):= clear hx (v:=200*X.B) (by change 30*X.B + separation t (S.ratio.parent x.1) ≤ _; omega)
   have hp' := ((h.safety.2.2.2 F X rfl hw hM).2 hT y hq R.beta hm.laws.intake.positive z h').2.1 x rfl
   rw [hm.laws.intake.received.temp] at hC; change toll Z x< X.t/4 at hp'; change X.t < toll Z x at hC; linarith

def demesne (R:Rep G f)(η a:ℝ) (A :ℕ→ Atom G p) (i:Trans f)(j:ℕ): Port.Test T := fun _ X w=> let K:= (primary G); let z:= worldZ X R.beta w
 if light X A i ∧ ¬ dim X i then η*pollen K X A i j z else Kiln.lantern K X a η A R i j z

-- for @ support-level propagation. Quantitative rare-event Horizon (Census Poll). Here debt of ONE retained interaction before amplifying. 
structure Astonish (H:Cash W s μ L Q o C T R)(Z:Support c) (j l:ℕ)(v d :ℝ)(χ:Chi)(a b:ℝ)(g:Port.Test T) : Prop where
   upheld : Port.Burst H Z g
   power : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (F:Forest S.ratio)(X:Coat T F)(V:E→ Config G c)(u:E→ Directions G f)(z:E→ Air f G)(x:E)(w:Air f G), X.x=s → X.width=o.K → X.manifest → X.χ=χ → Mode V x j v → Clutch X w o.a R.beta d x j V u z → ∀ U:Support c, Z ⊆ U →
     let K x:= g F (vary X (V x)) (z x)
     Brush j (a*facescale (edgesM S U (radiusB s)) w^l) b K x ∧ (w∉eerie X U (o.ξ/2) R.beta → K =ᶠ[𝓝 x] 0)
namespace Astonish
variable {t a t' a':ℝ}{f' : Port.Test T}{Z:Support c}
lemma raises (h:Astonish H Z j l v d χ a t f')(hv:l ≤ k)(hz: t≤t')(hn:a≤a')(he:0≤a) : Astonish H Z j k v d χ a' t' f':=by
 refine ⟨h.upheld,fun E _ _ _ F X V u z x w hv' hK hM hχ hf hg U he'=>?_⟩
 obtain ⟨hh,hX⟩:= h.power E F X V u z x w hv' hK hM hχ hf hg _ he'; refine ⟨hh.climb ?_ hz,hX⟩; have h :1≤facescale (edgesM S U (radiusB s)) w:= (Flux.expenses ..).1; gcongr; linarith
lemma null (ht:0≤t)(ha:0≤a): Astonish H Z j l v d χ a t (fun _ _ _=> 0):= by
 refine ⟨Port.Burst.fixed 0,fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=> ⟨(Brush.certified ht (0:ℝ)).climb ?_ le_rfl,fun _=> EventuallyEq.rfl⟩⟩; rw [norm_zero]; exact mul_nonneg ha (pow_nonneg (zero_le_one.trans (Flux.expenses ..).1) _)
end Astonish
end YM.LocalTaylorR2.Exponent
