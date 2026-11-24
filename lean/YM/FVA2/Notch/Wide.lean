import YM.MS.Vista.Meets
/-!
 # Angular geometry estimates for arbitrary fixed clearance (`c>0`).

 Analogues of `Vista.{Summer,Meets}`. Use any fixed positive fraction c of the
 actual period side measured in the sup norm (base-lattice metric; in physical
 units both sides would be multiplied by the spacing). Thus local anchors
 closer than fraction 1/16 can be treated. This lets us carry MS's Fourier
 remainder/Undo proof through all placements allowed in Sec:ms-quotient.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Notch
open Set Function Filter Finset Metric MeasureTheory Real Lattice MS MS.High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open MS.Rake.Geo MS.Orbit.LogReal MS.Vista
open scoped Topology ContDiff Interval
variable {G:Gauge} {I A':Type}{K:Belt I}{b:Bool}{L:I→Side}{A B:I→Cover}{n:Side}{r:ℝ}

abbrev wide (r:ℝ)(x:Lattice.Site n):Prop:= r*(n.val:ℝ)≤ (pdist x : ℝ)
def Adequate (L:I→Side) (x:I→Cover): Prop:= ∃ r:ℝ,0<r ∧ ∀ i,∀ z:Half, wide r (wrap (dimT L i) ( x i )- thin (L i) z)
lemma wide_neg (x: Lattice.Site n) : wide r (-x)↔ wide r x:= by simp [wide]
lemma wide_swap (x y: Lattice.Site n): wide r (x-y) ↔ wide r (y-x):= by rw [←wide_neg (x-y), neg_sub]
lemma wide_moon (k: Orbit.Zone n)(x:Half): wide r (k+thin n x)= wide r ( k-thin n x ):= by nth_rw 1 [u_car n x]; rw [sub_eq_add_neg]
lemma wide_twice (k:Orbit.Zone n)(h:∀ z: Half, wide r (k-thin n z)): wide r (k+k):= by
    unfold wide; rw [ altitude ]; let i:= (τ_frame n).parent k; obtain ht:= h i; unfold wide at ht; obtain he:= reduce (n:=n) k; rw [ Lattice.separation_comm,Lattice.separation ] at he; change pdist (k-thin n i)= _ at he; rw [he] at ht; push_cast; have he : 0≤ (pdist ( thumb n k ):ℝ):= by positivity
    push_cast [cap_val] at ht
    linarith
lemma paid_edge (x:Lattice.Site n)(h:wide r x) : ∃ a:Axis, r * tier ≤ |embed (Gates x) a * ψstep n| ∧ |embed (Gates x) a * ψstep n| ≤ tier-r*tier:= by
    unfold wide at h; obtain ⟨i,hi⟩:=axis_max x; obtain H:= ψpp n ; obtain hv:= sizeX x; obtain hm : 2*(pdist x:ℝ) ≤ n.val:=(by exact_mod_cast hv); obtain hz:= Bloch.side_pos n; obtain hT:= rising
    refine ⟨i,?_⟩; rw [abs_mul,abs_of_pos H, ← Real.norm_eq_abs, atτ,← hi]; unfold ψstep; rw [ ←mul_div_assoc ]; constructor
    · rw [_root_.le_div_iff₀ hz]; nlinarith [mul_le_mul_of_nonneg_right h hT.le]
    rw [_root_.div_le_iff₀ hz]; nlinarith [mul_le_mul_of_nonneg_right hm hT.le,mul_le_mul_of_nonneg_right h hT.le]
lemma pay_phase (hr:0<r)(h: ∀ i, wide r (wrap ( L i ) ( A i ))) : ∃ C:ℝ,0<C∧∀ i:I,∃ p:Axis, C ≤ ‖(1:ℂ)-( be (A i) (whole (ψstep (L i)) ( Lattice.step p )))⁻¹‖ := by obtain ⟨u,hu,hv⟩:= farBolt (mul_pos hr rising); refine ⟨ u,hu,fun i=>?_⟩; obtain ⟨p,hm⟩:= paid_edge (wrap ( L i ) ( A i )) ( h i ); refine ⟨ p,?_⟩; unfold be; rw [spanτ,bill_absneg ]; exact hv _ hm.1 hm.2
lemma angular (S:Scale I)(hp:∀ i,S.length i ≤ ( L i |>.val :ℝ ) )(H: ∃ r:ℝ, 0<r ∧ ∀ i, wide r ( wrap (L i) (A i))) : Radar S (fun i=> ( (L i).val:ℝ )) A (totalS ∘ L):= by
    obtain ⟨r,hr,H⟩:=H; obtain ⟨v,hv,hP⟩:= pay_phase hr H; choose P hp' using hP; let b(i):= ψstep (L i); let T(i):=whole (b i) (Lattice.step ( P i )); have ht(i):0<b i:=ψpp _; have he(i): ‖T i‖≤ b i := ( sharp (P i) (b i) )|>.trans_eq (abs_of_pos (ht i)); intro E _ _ f x hF j; obtain hm:= f_cap (Γ:=L) hp; obtain hx:= rapid_pay (T:=T) (μ:=totalS ∘ L) (S:=S) (U:=fun i=> be ( A i )) (fun i=> sailor _) hm.sector hF (fun i=>lounge (embed ( A i )) (T i)) (fun i=>( mul_le_mul_of_nonneg_left (he i) ( S.pos i|>.le))|>.trans (ν_engine hp i)) rising.le (fun i=> MS.Osc.Snap.boom ( ht i ) _ ) he v hv hp' (hm.mint E) j;
    refine hx.raise ⟨ tier^j,pow_pos rising _,0,fun i p _=>?_ ⟩; simp only [pow_zero,mul_one]; rw [ show S.length i * b i=tier*(S.length i/(L i).val) from (by unfold b ψstep; ring),mul_pow ]; exact le_of_eq (by ring)
local notation "Φ"=> Ap K (tickA L)
local notation "Ϝ"=> enterV L b
lemma separate_ge (h:∀ i:K.time,K.price.length i ≤ Φ i)(hv:MS.Vista.width L A)(hx:Adequate L A): Width K L Ϝ A:= by
 obtain ⟨r,hr,hD⟩:= hx; refine ⟨fun z=> ⟨ h,fun c=> ?_, net_quota (Fixed_paid z) hv ⟩, fun i j hi=> Act_p h ( Fixed_paid i ) ( Fixed_paid j) (block_core i j hi) ⟩
 apply angular (L:=Miles K L) K.price h; refine ⟨ r,hr,fun i=>?_⟩; change wide r ( wrap (dimT L i.1) ( env c (loci Ϝ z) A i.1 )); simp_rw [env,Dph,map_add,adjacent,ω_n]; cases c; · rw [ if_neg (by decide :¬false=true), ← sub_eq_add_neg ]; exact (wide_swap ..)|>.mpr ( hD i.1 z )
 rw [if_pos rfl,add_comm,wide_moon]; exact hD i.1 z
lemma rep_ge (hp:Adequate L A)(V:Visa I): RepT V L A:= by
   let K:= Mid V L; obtain ⟨r,hr,h⟩:= hp; refine ⟨angular (L:=Miles K L) K.price (fun i=> astral i ) ?_ ⟩; refine ⟨ r,hr,fun i=>?_⟩; unfold Miles dimT; rw [Ap,Vary, map_add ]; exact wide_twice _ (h i.1)
lemma cleared_ge (hp:Adequate L A)(he:MS.Vista.width L A) (V:Visa I): Place V L b A:={ mind := separate_ge (fun i=> astral i) he hp, after:=separate_ge (fun i=> (afterM i).le ) he hp, center:=rep_ge hp V }
end YM.FVA2.Notch
