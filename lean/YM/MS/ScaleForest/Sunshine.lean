import YM.MS.ScaleForest.TailBeam
/-!
# Port-to-port readouts for actual labels

Reach the position geometry used at the two marks of the drawing. The top
payoffs need positive separation. Keep the tensors and the scales through
the calculation in both cases, including the curl eigenvectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open Next Next.Rank Next.Rank.Beamer Next.Rank.Radian Prayer Aurora
open MS.Drops
open scoped Topology ContDiff BigOperators
variable {G : Gauge} (X Y:Pupil) (i j:Name G) (x:E4) (s:ℝ) (p:QP)

abbrev digit (a:PlaqAxes)(i:Name G) : Degree G:= ⟨ a,i.2,0,0,fun _=>0⟩
abbrev faces (a:PlaqAxes×PlaqAxes)(V:Degree G→Degree G→ℂ): ℂ:=(X.axes i.1 a.1 :ℂ)*(Y.axes j.1 a.2:ℂ)* V (digit a.1 i) (digit a.2 j)

lemma axial (a:PlaqAxes) (w:Shaft G 0) : rampLeg a i w.2 p w.1=fax (digit a i) (armI (m:=0) w p) := by
   obtain ⟨j,k⟩:= w; obtain ⟨⟨u,v⟩,h⟩:= a; have he:u≠v:= (show u < v from h).ne
   rw [show fax _ _ = if j=i.2 then axisC u v k p else 0 from ?_]; swap; · have hx:= photo (digit ⟨⟨u,v⟩,h⟩ i) k j p; simpa [ GlowD,digit ] using hx
   unfold rampLeg; split; next ht=>
       rw [axis_eq _ _ _ _ he]; unfold Coil polar0 Landau.delta; simp only [six,endr,show ∀ x:Axis,chair 0 x=x from fun x=>rfl]; split_ifs <;> first| (solve| tauto) | (push_cast; ring)
   rfl

def portfolio (i':Name G) (j':Name G) (p:QP) := ∑ a:Shaft G 0, Cur X i' p a*Cur Y j' (-p) a
lemma spectrum : portfolio X Y i j p= ∑ a:PlaqAxes×PlaqAxes,faces X Y i j a (fun L K=> Drops.xy (fax L) (fax K) p) := by
   unfold portfolio Cur antenna; simp_rw [axial]
   let f (r:PlaqAxes×PlaqAxes)(u:Shaft G 0):ℂ:= faces X Y i j r fun L K=>fax L (armI (m:=0) u p) * fax K (armI (m:=0) u (-p));
   rw [show (∑ u:Shaft G 0, _ ) = ∑ u:Shaft G 0,∑ r:PlaqAxes×PlaqAxes,f r u from ?_, Finset.sum_comm]; swap; ·
       apply Finset.sum_congr rfl; intro a _; rw [ Fintype.sum_prod_type ]; simp_rw [Finset.sum_mul, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; unfold f faces; ring
   apply Finset.sum_congr rfl; intro k _; unfold f faces; rw [← Finset.mul_sum,Fintype.sum_prod_type]; rfl

-- physical Fourier valuation gluing.
abbrev Φ (p:E4)(q : QP) := Tone.bill (Theater.out p) q

private theorem collect_mu (d:(QP→ℂ))(h:∀ a b:Degree G, Integrable (fun p:QP=> Φ x p * (xy (fax a) (fax b) p *d p) ) planeF) :
    Integrable (fun p:QP=> Φ x p * (portfolio X Y i j p*d p)) planeF ∧
    (∫ p:QP, Φ x p * (portfolio X Y i j p*d p) ∂planeF) = ∑ a:PlaqAxes×PlaqAxes,faces X Y i j a (fun L K=> ∫ p:QP, Φ x p*(xy (fax L) (fax K) p*d p)∂planeF) := by
    let f a (p:QP):=faces X Y i j a fun L K=> Φ x p*(xy (fax L) (fax K) p*d p)
    have he (a:PlaqAxes×PlaqAxes): Integrable (f a) planeF:= (h _ _).const_mul _
    have hp (p:QP): Φ x p*(portfolio X Y i j p * d p)=∑ a:PlaqAxes×PlaqAxes,f a p:= by
       rw [spectrum]; simp_rw [Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; unfold f faces; ring
    simp_rw [hp]; refine ⟨ integrable_finsetSum _ fun i _=> he i,?_⟩; rw [integral_finsetSum _ fun i _=> he i]; unfold f faces; simp_rw [ integral_const_mul ]

def salute' (p:QP)(s:ℝ):= Φ x p*(portfolio X Y i j p* shining (m:=0) p s)
def sunRise := ∑ a:PlaqAxes×PlaqAxes,faces X Y i j a (fun L K=> firstS L K x s)
def sunDot := ∫ p:QP, salute' X Y i j x p s ∂planeF
lemma sunAmount : sunDot X Y i j x s=∑ a:PlaqAxes×PlaqAxes,faces X Y i j a fun L K=> sunny L K x s := by
   unfold sunDot; have h:= collect_mu X Y i j x (fun p=> shining (m:=0) p s) (fun i j=> shine_int i j x s); rw [ show (fun L K:Degree G=> sunny L K x s)=_ from ?_ ]; exact h.2; exact funext (fun i=> funext fun j=>terminal_launch i j x s)
lemma sunSupported : Integrable (fun p=>salute' X Y i j x p s) planeF:= (collect_mu X Y i j x _ (fun a b=>shine_int a b x s)).1
lemma sunSpeed : HasDerivAt (sunRise X Y i j x) (sunDot X Y i j x s) s:= by rw [sunAmount]; exact HasDerivAt.fun_sum fun L _=> (first_d ..).const_mul _
def sunLimit := ∑ a:PlaqAxes×PlaqAxes,faces X Y i j a (fun L K=> ( gleam L K x:ℂ ))
lemma sunSets : Tendsto (sunRise X Y i j x) atTop (𝓝 (sunLimit X Y i j x)):= tendsto_finsetSum _ fun _ _=> (first_top ..).const_mul _
lemma sunStart (h:x≠0): Tendsto (sunRise X Y i j x) atBot (𝓝 0):= by
    unfold sunRise; convert tendsto_finsetSum Finset.univ (fun a (ha:a∈Finset.univ)=> (first_out (digit (Prod.fst a) i) (digit a.2 j) x h).const_mul ((X.axes i.1 a.1:ℂ)* (Y.axes j.1 a.2:ℂ))) using 1; simp -- implicit binding

-- repeat-line length W+ rises. include color. HTOP;
def salute₂ (p:QP)(s:ℝ):= salute' X Y i j x p s * Highβ G (m:=0) p s -- only ONE ordering

def moonRise := Coupling G *∑ a:PlaqAxes×PlaqAxes,faces X Y i j a (fun L K=> topFlow L K x s)
def moonDot := 2*∫ p:QP, salute₂ X Y i j x p s ∂planeF
lemma salute_full (p:QP): 2 * salute₂ X Y i j x p s= Coupling G * (Φ x p *(portfolio X Y i j p*pearler p s)) := by
    unfold salute₂ salute' Highβ pearler; ring
lemma moonAmount : moonDot X Y i j x s=Coupling G*∑ a:PlaqAxes×PlaqAxes,faces X Y i j a fun L K=> tapFlow L K x s := by
    have h:= collect_mu X Y i j x (fun p:QP=> pearler p s) (fun a b=> cumInt a b s x); unfold moonDot; rw [ ← integral_const_mul ]; simp_rw [ salute_full,integral_const_mul,costFlow ]; rw [h.2]
lemma moonSupported : Integrable (fun p=>salute₂ X Y i j x p s) planeF:= by
    obtain h:= ( collect_mu X Y i j x (fun p=> pearler p s) (fun a b=> cumInt a b s x) ).1;
    let u(k:QP):= salute₂ X Y i j x k s; let f(k:QP):=Φ x k*(portfolio X Y i j k * pearler k s)
    convert (h.const_mul (Coupling G/2)) using 1; funext k; change u k = (Coupling G/2)* f k; apply mul_left_cancel₀ (a:=(2:ℂ)) (by norm_num); rw [ ← mul_assoc, show (2:ℂ)*(Coupling G/2)=_ from (show _=Coupling G from by ring) ]; exact salute_full X Y i j x s k
lemma moonSpeed : HasDerivAt (moonRise X Y i j x) (moonDot X Y i j x s) s:= by rw [moonAmount]; exact ( HasDerivAt.fun_sum fun a _=> (life_top ..).const_mul _ ).const_mul _
lemma moonSets : Tendsto (moonRise X Y i j x) atTop (𝓝 (Coupling G * sunLimit X Y i j x)):= ( 
    (tendsto_finsetSum ( Finset.univ (α:=PlaqAxes × PlaqAxes) ) fun a _=> (terminal_paid_top (digit a.1 i) (digit a.2 j) x rfl rfl).const_mul _)).const_mul _
lemma moonStart (h:x≠0) : Tendsto (moonRise X Y i j x) atBot (𝓝 0):= by
    unfold moonRise; convert (tendsto_finsetSum Finset.univ (fun a (ha:a∈Finset.univ)=> (terminal_paid_start (digit (Prod.fst a) i) (digit a.2 j) x h rfl rfl).const_mul ((X.axes i.1 a.1:ℂ)*(Y.axes j.1 a.2:ℂ)))).const_mul (Coupling G) using 1; simp
end YM.MS.ScaleForest.Triangle
