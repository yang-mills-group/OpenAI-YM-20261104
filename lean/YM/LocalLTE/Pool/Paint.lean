import YM.LocalLTE.Crafts.Canal
import YM.Extra.WILSON_STARTUP.Cake
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
variable (G : Gauge) {n : Side} {j M:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
lemma primeP (j:ℕ) : ∃ p:ℝ,0≤p∧∀ (n:Side)(i:WilsonStartup.Cell n)(v:Directions G n), ‖v‖≤ 1 →Brush j p 1 (residual G i∘soloV) v:=by
    obtain ⟨c,hc,H⟩:=LocalLTE.Cabana.thick G j
    let f:= Quad.surplusMat (G:=G); let V:= Blaze.royalty G; let P:=4*(c*V); let M:=V*(1+P)^j; have hp:0≤M:= by unfold M P V; have hz:=(royalty_ge G); positivity
    obtain ⟨v,hv,h⟩:= Blaze.Brush.compact (f:=f) (isCompact_closedBall (0:G.Mat) M) (fun x _=> (@Quad.surplusMat_diff G).contDiffAt.of_le (show (↑j:WithTop ℕ∞)≤ ω from le_top)) -- edit Universe
    refine ⟨j.factorial*v*(1+(1+M))^j,by positivity,fun n i x hx=>?_⟩
    let t (u:Directions G n):= G.mat (faceValue (soloV u) i); let q:= square i.2.val.1 i.2.val.2; let S:= H n x hx
    have he:Brush j V P t x:= by convert (Blaze.tour q i.1 S.pos S.atLink) using 1; rw [show q.length=4 from rfl]; norm_num [P,V]; rfl
    have hh:Brush j _ 1 t x:= he.trim; have ht : ‖t x‖≤M:= by
       have hv:= (Brush.offer.mp hh).2 0 (Nat.zero_le _); simpa [normJ] using! hv
    have hg: Brush j (j.factorial*v) (1+M) (fun y=> f (t y)) x:= Brush.trail (h:=show (0:ℝ)<1 from one_pos) (h _ (mem_closedBall_zero_iff.mpr ht)) (hh.climb (show M ≤ M*1 from (mul_one ..).symm.le) le_rfl) (by norm_num)
    apply hg.trim.shimmy; filter_upwards with i'; exact (Quad.surplus_actual (faceValue (soloV i') i)).symm
-- Radius =3. support4. even Blank -> set zeros irrespective old. Comic base.
section width
variable {G} {κ k:ℝ} {P:BudgetPoint}(h:Reliable G κ k)
def shore' (i : Key n):= neighbors 4 i.native
-- edit Seat.Anchor.Signed
abbrev ew (i:Site n):RegularAddress n:=⟨i,neighbors 4 i,(neighbors_mem ..).2 (by simp)⟩
def glaze (G:Gauge)(i:PlaqAxes)(κ:ℝ)(j:ℕ) : Pot G n := PriceBlock (cane 0) where PriceBlock A:= Hall.shave A 3 κ (pie j+1) (residual G (0,i))
abbrev draft (G:Gauge)(i:Key n)(κ:ℝ)(j:ℕ):= glaze G i.2.2 κ j ∘ i.frame
lemma shore'₀ (i:Key n): i.skin ⊆ neighbors 3 i.native:=fun x hx=> (neighbors_mem ..).2 ((by have h:= Key.nearby i hx; omega)) -- edit direction
lemma res_ne (c:Side)(i:PlaqAxes): touched ((0,i):Cell c) ⊆ neighbors 3 (0:Site c):= by
   intro v hv; have he:= WilsonStartup.visit_near ((0,i): Cell c) hv; apply (neighbors_mem ..).2; simp only at he; rw [separation_comm] at he; omega
lemma shore_l (o:Site n) : neighbors 3 o ⊆ neighbors 4 o:= Corona.halo_mono (by norm_num) (Finset.Subset.refl _)
def boat (i:Key n):Seat n:= (i.1,i.native)
lemma shiftE (i:Key n): i.native=affine (Frost.boat i).1 (Frost.boat i).2 (0:Site n):= by simp [Frost.boat,Lattice.affine]
lemma sp_k (i:Key n): neighbors 4 i.native= (Frost.boat i).spread (neighbors 4 0):= (normRange (shiftE i) 4).symm

lemma plot (P: BudgetPoint)(h:Reliable G κ k)(hg:G.Simple)(hn:20<n.val)(j:ℕ)(i:Key n): Comic G (ew i.native) P (draft G i κ j) := by
    let Z:= (i.root); let f':= residual G Z
    have ht:P.Regular (neighbors 3 (0: Site n)) f':= VerifiedReset.reg_larger (residual_regular Z P) (Frost.res_ne _ _)
    have hF : ContDiffAt ℝ (↑(pie j+1): WithTop ℕ∞) (f' ∘ soloV) 0:= by rw [← Hall.bare]; exact ((residual_smooth Z 1).of_le le_top).contDiffAt
    exact (Price.staple (X:=cane (0:Site n)) P 3 h f' ht hF (neighbors 4 (0:Site n)) (shore_l _) (ew (0:Site n)).anchor (residual_one ..) (fun _ v w _ _=> residual_hess ..)).move hg hn (boat i) _ (shiftE _) (sp_k i)
end width
variable {L: Side}{u t μ κ :ℝ}{A:Side}{Q: Stage}{P: BudgetPoint}
open LocalLTE.Inset
lemma can (L:Side) (κ:ℝ)(h:Reliable G κ u) (A: Stage)(j:ℕ) : ∀ᶠ t in atTop, (∀ P:BudgetPoint, P.order=A.order→P.power=A.power→ P.threshold=Pressure.temp t → P.threshold ≤ 2*Pressure.fiery G t L→ ∀ (n:Side)(_ :20<n.val)(o:PlaqAxes), P.supBounds (0:Site n) (neighbors 4 (0:Site n)) (residual G (0,o)-glaze G o κ j) ((betaF G t L)^(Urns.dust j-1))) := by
    obtain ⟨C,hp,hQ⟩:= Frost.primeP G (pie j+1+A.order)
    let f:= fun _:ℝ=>C
    have hC: Rate G L 0 f:= Rate.const _
    have hx: Rate G L 0 (fun _=> ((4:ℕ):ℝ)):= Rate.const _
    have hv:0+ Urns.clr*(↑(pie j+1):ℝ) < Urns.dust j-1:=by unfold clr pie Urns.dust chip; push_cast; linarith
    filter_upwards [Hall.prunes G L A.order A.power (pie j+1) (n:=fun _=>4) hx h (by norm_num [clr]) (by norm_num [clr]) hC hv,(Rate.power (G:=G) (L:=L) (a:= Urns.clr)).below (by norm_num [clr]) 1 zero_lt_one] with x hx hh P hP hO ht hB n hN o
    let q:= residual G ((0,o): WilsonStartup.Cell n)
    refine VerifiedReset.sup_le (hx P hO hP ht hB 4 3 le_rfl (by omega) _ (0: Site n) (by omega) (by omega) (cane 0) q (VerifiedReset.reg_larger (residual_regular _ P) (Frost.res_ne n _)) 1 zero_le_one ?_) ((one_mul _).le)
    intro u hu; rw [one_mul]; exact hQ n _ u (hu.le.trans ((le_abs_self _).trans hh))
lemma mist {i:Key n} {κ K:ℝ} (h:Reliable G κ K)(j:ℕ) (hQ: P.supBounds (0:Site n) (neighbors 4 (0:Site n)) (residual G (0,i.2.2) - glaze G i.2.2 κ j) t) : P.supBounds i.native (neighbors 4 i.native) (i.accrual-draft G i κ j) (turnFee P*t):=by
    let v:= boat i
    have he: P.Regular (neighbors 4 (0:Site n)) (residual G (0,i.2.2)-glaze G i.2.2 κ j):= reg_larger (VerifiedReset.reg_sub (VerifiedReset.reg_larger (residual_regular _ P) (Frost.res_ne n _)) (LocalLTE.FrameBox.legal _ _ h _ _)) (shore_l _)
    have ht:= Song.transSup (boat i) he hQ; rw [← sp_k i, ← shiftE i] at ht; exact ht
end YM.WilsonStartup.Frost
