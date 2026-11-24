import YM.XSpace.Marque

/-!
# Charge payments at a lattice reading
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Tide
open Function Filter Set Trace Scale Lattice Sail Litter Further.FreeCovariance.KP
open Maxwell (grad)
open scoped Topology BigOperators ContDiff
variable {k n m d:ℕ} {G:Gauge} {ι:Type}{L:Filter ι} {r:ι→ℕ} {x y z:ι→Cover}{u:E4}{a:ι→ℝ}

lemma foil_ask {j:ℕ}{p:Line G}(H:p∈ cane j G): ∃ (f:Rudder G j→₀ℝ),∀ x:Cover, ∀ A:Contact G,
    probe (displace x p) A= ∑ i∈f.support,f i*crack (List.ofFn i.layout) (Scale.twig i.head.1.2 A) (x+i.head.1.1) i.head.2 :=by
  obtain ⟨w,rfl⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp H -- verify
  refine ⟨w,fun x A=>?_⟩; rw [Finsupp.sum,map_sum,map_sum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl; intro i _; rw [map_smul,map_smul,LinearMap.smul_apply,Rudder.worth,toll,pin,in_gate]; rfl
lemma rate_flags {p:Line G}(H:p∈cane k G) : ∃ C:ℝ, 0≤C∧∀ (A:Vase n G.Color) (x:Cover),
     |probe (displace x p) (release A)| ≤ C*‖A‖*(1+reach x)^(n-k) :=by
  obtain ⟨f,h⟩:= foil_ask H; choose B hB H using fun i:Rudder G k=> pay (F:=G.Color) (List.ofFn i.layout) (half i.head.1.2) n
  let D (i:Rudder G k):ℝ := 1+reach i.head.1.1; have hd i : 0<D i:=by unfold D; positivity
  refine ⟨∑ i∈f.support, |f i| * B i*(D i)^(n-k),Finset.sum_nonneg fun i _=>by positivity [hd i,hB i],fun A x=>?_⟩
  rw [h, Finset.sum_mul,Finset.sum_mul]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_); set z:=i.head; set j:=z.1.2; set y:=x+z.1.1; let b:ℝ:=1+reach x; set m:=n-k
  have hb:0<b:=by unfold b; positivity
  specialize H i y (A j); rw [List.length_ofFn] at H; have he : (1+(reach y:ℝ)) ≤ D i*b:=by
    have he: (reach y:ℝ) ≤ (reach x:ℝ)+(reach z.1.1:ℝ):=by exact_mod_cast tree x z.1.1
    have hd: D i=1+↑(reach z.1.1):=rfl; rw [hd]; unfold b; nlinarith [Nat.cast_nonneg (reach z.1.1) (α:=ℝ),Nat.cast_nonneg (reach x) (α:=ℝ)]
  rw [abs_mul]; calc
    _ ≤ |f i| *(B i*‖A j‖*(1+(reach y:ℝ))^m):= mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (felt (half j) (A j) (List.ofFn i.layout) y) z.2).trans H) (abs_nonneg _)
    _ ≤ |f i| *(B i*‖A‖*(D i*b)^m):= by have hh:=hB i; gcongr; apply norm_le_pi_norm
    _ = _:= by rw [mul_pow]; unfold b; ring
lemma vacuity {u:Line G}(h:u∈cane k G)(hp:n<k) (A: Vase n G.Color)(x:Cover): probe (displace x u) (release A)=0:=by
  obtain ⟨f,he⟩:=foil_ask h; rw [he]; apply Finset.sum_eq_zero; intro i _; change f i * felt (half i.head.1.2) (A _) (List.ofFn i.layout) _ _= _; rw [late _ _ (by simpa using hp),show ∀ x c,(0:Cover→G.Color) x c=0 from fun _ _=>rfl]; simp

lemma line_receipt {p q:Line G}(H:p∈ cane k G){X:Radio G.Color}(K:Wave d q X):∃ C:ℝ,0≤C ∧ ∀ x: Cover, |handshake (displace x p) q| ≤ C*carry (2+d+k) (reach x):=by
  obtain ⟨f,h⟩:=foil_ask H; choose C hC Hx using fun i:Rudder G k=> (K i.head.1.2).glows (List.ofFn i.layout); let n:=2+d+k; let D (i:Rudder G k):= (1+(reach i.head.1.1:ℝ)) -- specify type
  refine ⟨∑ i ∈ f.support, |f i| *C i*(D i)^n,Finset.sum_nonneg fun i _=>by unfold D; positivity [hC i],fun x=>?_⟩; unfold handshake; rw [h,Finset.sum_mul]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_); rw [abs_mul,mul_assoc _ (D i^n),mul_assoc |f i|]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); have hx:=Hx i (x+i.head.1.1); rw [List.length_ofFn] at hx; have he:= PiLp.norm_apply_le (crack (List.ofFn i.layout) (Scale.twig i.head.1.2 (bake q)) (x+i.head.1.1)) i.head.2
  apply (he.trans hx).trans; apply mul_le_mul_of_nonneg_left _ (hC i); apply phase_cost; rw [← reach_neg i.head.1.1]; exact le_trans (le_of_eq (by rw [add_neg_cancel_right])) (tree ..)

-- general schedule read bound; with ball cutoff x & test. choose common with highest target degree.
lemma parcel {p:Line G}(H:p∈cane k G){A:ι→Contact G} {w:ι→ℝ}(h:∀ t:Fin k→Axis,∀ j:Axis,∃ C:ℝ,0≤C∧∀ᶠ i in L,∀ x:Cover,reach x≤r i→ ‖crack (List.ofFn t) (Scale.twig j (A i)) x‖ ≤ C*w i*(1+reach x)^n)(hp:∀ᶠ i in L,0≤w i):
    ∃ (C:ℝ)(u:ℕ),0≤C∧∀ᶠ i in L,∀ x:Cover, reach x+u ≤r i→ |probe (displace x p) (A i)| ≤ C*w i*(1+reach x)^n:=by
  obtain ⟨f,hf⟩:= foil_ask H; choose C hC Hx using fun i:Rudder G k=> h i.layout i.head.1.2; let u:= f.support.sup fun i=> reach i.head.1.1; let D:ℝ:=1+u
  have hd :0≤D:= by unfold D; positivity
  refine ⟨∑ i∈f.support, |f i| *C i*D^n,u,Finset.sum_nonneg fun i _=>by positivity [hC i],?_⟩
  filter_upwards [(Filter.eventually_all_finset f.support).mpr (fun i _=>Hx i),hp] with i hi hw x hx; rw [hf,Finset.sum_mul, Finset.sum_mul]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j hj=>?_); let m:=j.head; let r':=reach x; let y:=x+m.1.1
  have hu : reach y ≤ r'+u:= (tree ..).trans (Nat.add_le_add_left (Finset.le_sup (f:=fun j=> reach j.head.1.1) hj) _)
  have he : (1+(reach y:ℝ)) ≤ D*(1+r'):= by
    unfold D
    have he:(reach y:ℝ)≤(r':ℝ)+u:=by exact_mod_cast hu
    nlinarith [Nat.cast_nonneg r' (α:=ℝ),Nat.cast_nonneg u (α:=ℝ)]
  rw [abs_mul]; apply (mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (crack _ _ y) m.2).trans (hi j hj y (hu.trans hx))) (abs_nonneg _)).trans; have hh:=hC j
  change _≤ _; calc
    _ ≤ |f j| * (C j*w i*(D*(1+r'))^n):= by gcongr |f j| * (C j*w i* ?_^_ )
    _ = _:= by rw [mul_pow]; unfold r'; ring
private lemma parcel_o {p:Line G}(H:p∈cane k G){A:ι→Contact G}{w:ι→ℝ}(h:∀ t:Fin k→Axis,∀ j:Axis,∃ C:ℝ,0≤C∧∀ᶠ i in L,∀ x:Cover,reach x≤r i→ ‖crack (List.ofFn t) (Scale.twig j (A i)) x‖ ≤ C*w i)(hp:∀ᶠ i in L,0≤w i):
    ∃ (C:ℝ)(u:ℕ),0≤C∧∀ᶠ i in L,∀ x:Cover, reach x+u ≤r i→ |probe (displace x p) (A i)| ≤ C*w i:=by
  have he := parcel (n:=0) (A:=A) (r:=r) H (by simpa using h) hp; simpa using he
lemma steady_price {A:ι→Contact G}(S:Studio L a r A)(h:∀ᶠ i in L,0≤a i){p:Line G}(H:p∈cane k G):
    ∃ (C:ℝ)(u:ℕ),0≤C∧∀ᶠ i in L,∀ x:Cover, reach x+u≤r i → |probe (displace x p) (A i)| ≤ C*a i^(1+k):=by
  obtain ⟨C,hC,hp⟩:= S.loans k; exact parcel_o (w:=fun i=>a i^(1+k)) H (fun t j=> ⟨C,hC,hp.mono (fun i hi x hx=> hi x hx _ (List.length_ofFn) _)⟩) (h.mono fun i hi=> by positivity)
lemma remainder_price {A:ι→Contact G}(S:Studio L a r A)(h:∀ᶠ i in L,0≤a i){p:Line G}(H:p∈cane k G)(he:k≤d+1):
    ∃ (C:ℝ)(u:ℕ),0≤C∧∀ᶠ i in L,∀ x:Cover, reach x+u≤r i → |probe (displace x p) (A i-scenic d (gather d (A i)))| ≤ C*a i^(d+2)*(1+reach x)^(d+1-k):=
  parcel H (w:=fun i=> a i^(d+2)) (A:= fun i=> A i-scenic d (gather d (A i))) (fun t j=> by simpa using S.rehearsed h (List.ofFn t) j (by simpa using he)) (h.mono fun i hi=> by positivity)

-- target stencil limit read on harmonic Stamp-mode letter; can supply any smooth tensor here

def scored {X:Radio G.Color}(h:∀ j,ContDiffAt ℝ ∞ (X j) u)(k:ℕ): Vase k G.Color:= fun j=>⟨Tensor.coeff (X j) k u, Tensor.coeff_symm ((h j).of_le (WithTop.coe_le_coe.mpr le_top))⟩
lemma prunes {X:Radio G.Color}(h:∀ j,ContDiffAt ℝ ∞ (X j) u){A:ι→Contact G}{p:Line G}(H:p∈cane k G)(t:ι→ℝ)(hz:∀ v:Cover,∀ l:List Axis,∀ j:Axis,l.length=k→Tendsto (fun i=> t i • crack l (Scale.twig j (A i)) (x i+v)) L (𝓝 (ride l (X j) u))):
    Tendsto (fun i=> t i*probe (displace (x i) p) (A i)) L (𝓝 (probe p (release (scored h k)))):=by
  obtain ⟨f,hf⟩:= foil_ask H; nth_rw 2 [show p=displace 0 p from (originate p).symm]; simp_rw [hf,Finset.mul_sum,zero_add]; apply tendsto_finsetSum _; intro i _; let m:=i.head; let s:=i.layout; let v:=m.1.1; let c:=m.1.2; let z:=scored h k c
  specialize hz v (List.ofFn s) c List.length_ofFn; have he : Tendsto (fun j=>f i*( (t j • crack (List.ofFn s) (Scale.twig c (A j)) (x j+v)) m.2 )) L (𝓝 (f i* (ride (List.ofFn s) (X c) u m.2))):= Tendsto.const_mul _ ((EuclideanSpace.proj m.2).continuous.continuousAt.tendsto.comp hz)
  rw [show crack _ (Scale.twig _ (release _)) _=ride (List.ofFn s) (X c) u from ?_]; exact he.congr (fun j=> mul_left_comm (f i) _ _)
  rw [rode s (h c)]; exact sent (half c) z v s
lemma paid_pair {p q:Line G}{X:Radio G.Color}(H:p∈cane k G)(K:Wave d q X)(hu:u≠0)(hx:Tendsto (fun i=> a i • rcast (x i)) L (𝓝 u))(hp:∀ᶠ i in L,0<a i)(h:Tendsto a L (𝓝 0)) :
    Tendsto (fun i=> (a i)⁻¹^(2+d+k)*handshake (displace (x i) p) q) L (𝓝 (probe p (release (scored (fun j=>(K j).value u hu) k)))):= by
  apply prunes (A:=fun _=> bake q) (fun j=>(K j).value u hu) H; intro v l j hl; rw [← hl]; apply (K j).beams hp h (x:=fun i=> x i+v) _ hu; simp_rw [Cross.rcast_add, smul_add]; simpa using hx.add (h.smul_const (rcast v))
end YM.XSpace.Tide
