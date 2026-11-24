import YM.SignedWilsonExpansion.AxialBill
namespace YM.SignedWilsonExpansion.Overlap.Marque
/-! # Color physical coefficients on low horizon 4. Prescribed trader θ₀ and
    off-axis layquettes. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Plane MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land MS.Puff MS.Puff.Mom MS.Puff.SplitP MS.Puff.Engine MS.Puff.Actors
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace Contrast PairWave
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:ℕ}
local notation "N" => Fintype.card G.ColorIndex
local notation "i₀" => (3:Idx)
def reflectQ (y:E4)(u w:Idx):ℝ:= wedge (house y).val (Normalize.left u) (Normalize.right u) (Normalize.left w) (Normalize.right w)
variable (q:Stage n)(i j k:Fin n)(h:i≠j)(hk:i≠k)(hl:j≠k)
local notation "Y" => (q.val.ofLp)
def ticket (u w:Idx):ℝ:=pay q i j * reflectQ (q.val i-q.val j) u w
lemma complement (z:E4): reflectQ z 2 3=0:= by change wedge _ 0 3 1 2=_; simp [wedge,Free.house,houseM,kr_eq]; ring
lemma complimentary : ticket q i j 2 3=0:= by rw [ticket,complement,mul_zero]
include h
lemma atom (c d:G.ColorIndex)(u w:Idx): linkEntry (Y i, bin u c) (Y j,bin w d)= if c=d then (ticket q i j u w:ℂ) else 0:= by
    let x:=Y i; let y:=Y j; have hh:x≠y:=( show Injective Y from q.property ).ne h
    rw [ link_eq _ _ _ _ hh ]; change ( ( Free.K (omegaLeg c (Normalize.left u) (Normalize.right u)) (omegaLeg d (Normalize.left w) (Normalize.right w)) x y ):ℂ)=_; rw [ omega_K_eq _ _ _ _ _ _ hh ]; split_ifs; · rw [ bare_formula _ _ _ _ ( sub_ne_zero.mpr hh ) ]; rfl
    exact Complex.ofReal_zero
omit h in
private lemma stock (u v:Idx) : wmark G u v=∑ a:G.ColorIndex,WickFace.ψ (bin u a) (bin v a):= rfl
local notation "b" => WickFace.ψ
lemma chargeP (a d u:Idx): dyad q i j (wmark G u u) (wmark G a d)= ((N:ℝ)*2*ticket q i j a u * ticket q i j d u:ℝ):= by
    rw [stock a d,map_sum]; have hx (a d:Factor G) : dyad q i j (wmark G u u) (b a d)= ∑ w:G.ColorIndex, dyad q i j (b (bin u w) (bin u w)) (b a d):= by rw [mate q _ _ _ _ h,stock,map_sum]; exact Finset.sum_congr rfl fun c _=> mate q _ _ _ _ h.symm
    simp_rw [ hx,WickFace.price_pair q i j h, atom q i j h ]; simp only [ mul_ite,ite_mul,mul_zero,zero_mul ]; simp; ring
include hk hl
lemma chargeT (a:Idx): journey q i j k (wmark G i₀ i₀) (wmark G i₀ i₀) (wmark G a a)= ( N*8*ticket q i j a i₀ * ticket q i k a i₀ * ticket q j k i₀ i₀:ℝ):= by
    rw [stock a a,map_sum]; have he(a d:Factor G) (j k:Fin n)(S:WickPol G)(hx:i≠j): journey q i j k (wmark G i₀ i₀) S (b a d)=∑ u:G.ColorIndex, journey q i j k (b (bin i₀ u) (bin i₀ u)) S (b a d):= by
       rw [ front q _ _ _ _ _ _ hx,stock,map_sum ]; exact Finset.sum_congr rfl fun _ _=> front q _ _ _ _ _ _ hx.symm
    have hq(a d:Factor G)(S:WickPol G):journey q i j k S (wmark G i₀ i₀) (b a d)=∑ u:G.ColorIndex, journey q i j k S (b (bin i₀ u) (bin i₀ u)) (b a d):= by
       rw [ rear q _ _ _ _ _ _ hl, he _ _ k _ _ hk ]; exact Finset.sum_congr rfl fun _ _=> rear q _ _ _ _ _ _ hl.symm
    have hu (c:G.ColorIndex): (∑ u:G.ColorIndex, ∑ w:G.ColorIndex, journey q i j k (b (bin i₀ u) (bin i₀ u)) (b (bin i₀ w) (bin i₀ w)) (b (bin a c) (bin a c)))= ((8*ticket q i j a i₀ * ticket q i k a i₀ * ticket q j k i₀ i₀:ℝ):ℂ):= by
       simp_rw [ price_trip q i j k h hl hk, atom q i j h,atom q i k hk,atom q j k hl ]; -- finish sums
       rw [ Finset.sum_eq_single_of_mem c (mem_univ _) ]; swap; · intro a' _ h; simp [Ne.symm h]
       rw [ Finset.sum_eq_single_of_mem c (mem_univ _ ) ]; swap; · intro a' _ h; simp [Ne.symm h]
       simp only [↓reduceIte]; push_cast; ring
    simp_rw [he _ _ _ _ _ h,hq, hu, Finset.sum_const]; simp; ring
omit h hk hl
def rail (w:Idx):ℝ:= if Normalize.right w =3 then -1 else 1
def exclusive (u w:Idx) :ℝ:= if u=w then 1 else 0
lemma axialH (v:ℝ)(hh:v≠0)(a d:Axis): houseM (timeLine v) a d=(if a=d then if d=3 then -1 else 1 else 0):= by
    have he:‖timeLine v‖^2=v^2:= by simp [norm_smul,timeLine]
    unfold houseM; rw [ Matrix.of_apply,kr_eq, he ]; by_cases hv':a=d <;> by_cases h':d=3 <;> simp [h', hv', timeLine] <;> field_simp <;> first| ring; done | split_ifs <;> ring
lemma voteLine (v:ℝ)(hh:v≠0)(u w:Idx): reflectQ (timeLine v) u w= exclusive u w * rail w:= by simp only [reflectQ, wedge,Free.house,axialH _ hh,exclusive, rail ]; fin_cases u <;> fin_cases w <;> simp (disch:=decide) [ Normalize.left, Normalize.right ]
include h
lemma costLine (H: Holds q)(u w:Idx): ticket q i j u w= pay q i j * ( exclusive u w * rail w ):= by unfold ticket; rw [ show reflectQ _ u w= _ from ?_ ]; obtain ⟨v,he⟩:= WickFace.gap q H i j; rw [he]; apply voteLine; intro h'; rw [h',timeLine,zero_smul] at he; exact sub_ne_zero.mpr ( (show Injective Y from q.property).ne h ) he
lemma dyAt (H:Holds q)(a d u:Idx): dyad q i j (wmark G u u) (wmark G a d)= ( N*2*pay q i j^2 * (exclusive a u*exclusive d u):ℝ):= by
    rw [chargeP q i j h,costLine q i j h H,costLine q i j h H]; unfold rail; split_ifs <;> push_cast <;> ring
omit h
variable (x:Stage 3)
local notation "K" => Fin 3
def actual (G:Gauge)(x:Stage 3)(u:Idx):ℝ:= ∑ i:K,Nof G*8*ticket x i (i+1) u i₀ * ticket x i (i+2) u i₀ * ticket x (i+1) (i+2) i₀ i₀
where
 Nof (G:Gauge):ℝ:=↑(Fintype.card G.ColorIndex)
lemma Xi_actual (u:Idx) : Xi G x (glow G u u)=((actual G x u):ℂ):= by
    rw [Xi, LinearMap.sum_apply]; unfold actual; push_cast; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ LinearMap.sub_apply, LinearMap.smul_apply ]; rw [ show coin (G:=G) x i (glow G u u) =0 from single_off x i u u,smul_zero, sub_zero ]; refine (chargeT x i (i+1) (i+2) ((by decide:∀ i:K,i≠i+1) i) ((by decide:∀ i:K,i≠i+2) i) ((by decide:∀ i:K,i+1≠i+2) i) u).trans ?_; push_cast; rfl
lemma void_w : actual G x 2=0:= by unfold actual; simp_rw [ complimentary, mul_zero,zero_mul ]; rw [ sum_const_zero ]
lemma bright : iris x ( Contrast.testE G 3 )= ( ( N*8*ticket x 0 1 i₀ i₀ * ticket x 0 2 i₀ i₀ * ticket x 1 2 i₀ i₀:ℝ ):ℂ):= by
     rw [← show update (testE G 3) 0 (lens G)=testE G 3 from update_eq_self .., Contrast.iris3 ]; exact chargeT x 0 1 2 (by decide) (by decide) (by decide) i₀
end
end YM.SignedWilsonExpansion.Overlap.Marque
