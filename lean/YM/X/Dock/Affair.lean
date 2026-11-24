import YM.X.Dock.Pebble
import YM.X.Dock.Trinket
/-!
## numerical amplitude in triangle prescription. includes factor conversions ray/ray powers. 

`bridge_angle` pp = horizon mixed curvature contour spin. p stencil coefficient
sum ds.A map. Integral extension in `Tracker`: ∂ off x; χ exterior, near x,y in
`Hatch` etc. near z chosen by integration by parts; matches single-line curl of D₀ convention via `Trinket`. No smoothness-in-marks theorem here.
No stress normalization yet. Spin under proper; Context use Theta in Pert.Position.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot Fund
open Maxwell Maxwell.Free Extra.FD Labels Pert.Position Pert.RawLabels
open Interval Size Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare Tri Pulse
open Chir.Dock Ribbon
open Finset
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {m k d:ℕ} {n:Side} {q a:ℕ+}{r R e c:ℝ}
local notation "A"=>Axis
local notation "L"=>(atTop:Filter ℕ)
local notation "T"=>Tet
variable (i u v:Tet)
abbrev eSpace (s:ℝ)(i:Tet)(x y:A):= rayS*form s i x y
abbrev mF (i:A)(t:Tet)(w x:E4):= rayS*Aster (-1) t i (x-w) -- sign
abbrev pF (i j:T)(z x:E4):= rayS^2* opportunity (z-x) i j 1 (-1)
variable {z x y:E4}(hx:z≠x)(hy:z≠y)
--- normalized p = Leg of Aster (second leg derivative w.r.t x). ∆.
include hx in
lemma bridge_angle : pF i u z x= ∑ a:A,∑ b:A, eSpace (-1) u a b* (rayS*Maxwell.grad a (fun v:E4=> Aster 1 i b (z-v)) x):= by
    -- explicitly charge via lattice ∆ limit; avoids index notation
    let q:ℕ+:=2; have hq:1<q.val:= by unfold q; decide
    let X:= fun k=>Haze.index (epsilon q k) x; let Z:= fun k=>Haze.index (epsilon q k) z; have ht: plot q X x:= entrant hq x; have hz:plot q Z z:= entrant hq z; let U(a b:A):=cable q Z X 2 (ds a (transfer 1 i b)); have he (a b:A):Tendsto (U a b) L (𝓝 (Maxwell.grad a (fun v:E4=> Aster 1 i b (z-v)) x)):= by rw [← sectionG 1 i a b z x hx]; exact (atlases 1 i a b hq).diff.edge hz ht hx
    let f k:= ∑ a:A,∑ b:A,eSpace (-1) u a b*(rayS* U a b k); have hf:Tendsto f L _:=tendsto_finsetSum Finset.univ fun a _ => tendsto_finsetSum Finset.univ (fun b _=> ((he a b).const_mul rayS).const_mul (eSpace (-1) u a b)); apply tendsto_nhds_unique _ hf -- fix
    apply ((starW hq hx hz ht i u 1 (-1)).const_mul (rayS^2)).congr; intro k; unfold f Wpp exchangeF U cable eSpace; simp_rw [sprite_val,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl (fun b _=> by ring)

abbrev A₀ (z x y:E4)(i m n:Tet):ℝ:= ∑ a:A,∑ b:A,eSpace 1 i a b *mF a m z x*mF b n z y
abbrev sumI (χ:Floor R)(x y z:E4)(i m n:Tet):ℝ:= ∑ t:Tet, rayS^5*overall χ x y z t m n i
abbrev tia (χ:Floor R)(z x y:E4)(i m n:Tet):= A₀ z x y i m n -2*sumI χ x y z i m n
-- ε contracted α = anti sum. formula
abbrev piUp (P Q:T→T→ℝ)(i u v:Tet): ℝ := ∑ j:T,∑ k:T, Chir.η i j k*P j u* Q k v
lemma accompany (P Q:Tet→Tet→ℝ): Α P Q i u v=piUp P Q i u v:= by
    fin_cases i <;> simp only [piUp,Α,Chir.η,loop,ℓ,Fin.sum_univ_three] <;> norm_num [←Fin.val_inj, fi3] <;> ring!
abbrev trians (G:Gauge)(χ:Floor R)(z x y:E4) := 6*Sage.count G*(∑ i:T,∑ m:T,∑ n:T, piUp (fun i j=>pF i j z x) (fun i j=>pF i j z y) i m n * tia χ z x y i m n)
local notation "S"=> rayS
variable (χ:Floor R)
include hx hy
lemma arm0 : A₀ z x y i u v=S^3* seedL x y z i u v:= by unfold A₀ seedL mF eSpace; simp_rw [symbol _ _ _ (sub_ne_zero.mpr hx.symm),symbol _ _ _ (sub_ne_zero.mpr hy.symm), Finset.mul_sum]; exact sum_congr rfl (fun i _=>sum_congr rfl (fun j _=> by ring))
lemma arm_tia : tia χ z x y i u v= S^3*(seedL x y z i u v-∑ t:T,overall χ x y z t u v i):= by
    unfold tia sumI; rw [arm0 i u v hx hy, ←Finset.mul_sum,← mul_assoc 2,show (5:ℕ)=3+2 from rfl,pow_add S,spark₂]; ring
lemma Tfull : trians G χ z x y= boostB*boostU*boostU*(4*Sage.count G*SpinLimit (overall χ x y z) x y z):= by
    have he(i u v:T): piUp (fun i j=>pF i j z x) (fun i j=>pF i j z y) i u v= S^4*Α (solar (z-x)) (solar (z-y)) i u v := by rw [←accompany]; unfold pF Α; simp_rw [leverage (sub_ne_zero.mpr hx),leverage (sub_ne_zero.mpr hy)]; ring
    unfold trians SpinLimit; simp_rw [he,fun i u v:T=> arm_tia i u v hx hy χ, Finset.mul_sum]; iterate 3
      refine Finset.sum_congr rfl (fun i _=>?_);
    unfold boostB boostU; ring
local notation "θ"=> (fun x:Points 3=> Complex.ofReal (trians G χ (x 0) (x 1) (x 2)))
omit hx hy
lemma targetT (hq:1<q.val)(B:Bare.Shop F)(hg:G.Simple)(hr:R<r)(t:Test 3)(h:Tri.ready B hg r)(hv:Curve t ⊆ Pulse.Region 3 r): Integrable (fun x:Points 3=>t x*(θ x))∧ firstX B q hq hg 6 3 t (beaconLabels F (Nat.le_refl 6))=t.applyTo θ:= by
    obtain ⟨he,hx⟩:= approved hq B hg χ hr t h hv; let U:= (Complex.ofReal (boostB*boostU*boostU)); let f(x:Points 3):=t x * ↑(earshot G χ x); have h₀:(fun x:Points 3=>t x*(θ x))= (fun x=> U*f x):= by
        ext1 x; by_cases he:t x=0; · simp only [f,he,zero_mul,mul_zero]
        have h:= hv (Subcell.includes (tsupport t) (subset_closure he)); have h'(i:Fin 3)(hw:i≠0): x 0 ≠ x i:= sub_ne_zero.mp (norm_pos_iff.mp ((χ.positive.trans hr).trans (h 0 (by simp) i (by simp) hw.symm))); unfold U f earshot; change t x * ↑(trians G χ (x 0) (x 1) (x 2))=_; rw [Tfull (h' 1 (by decide)) (h' 2 (by decide)) χ,Complex.ofReal_mul (boostB*_*_)];ring
    unfold Test.applyTo; rw [h₀,hx, integral_const_mul]; exact ⟨Integrable.const_mul he U,rfl⟩
end YM.PositionX.Bend
