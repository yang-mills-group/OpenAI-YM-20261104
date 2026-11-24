import YM.XSpace.DoublePole
/-!
# Extract a bilocal from three local quadratic probes

Uses exactly real disjoint points for both terminals. With arbitrary spectators
allowed in the linear identity, keep two terminals at the desired points, run
one common pole coordinate on the third; this guarantees one uncontracted
line at each terminal. The terms with doubled contractions to a terminal
have the same total pole order, so pay for those via detached identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge} {S:Set E4}{m u v:E4}
local notation "x" => (m+v)
local notation "y" => (m-v)
variable (c:G.ColorIndex)(p:Flavor 0)(i:G.ColorIndex)

lemma double_sign {z:E4} (q:Flavor 0) {C':ℂ} (h:∀ j:G.ColorIndex, Receiving m u v p i (singleF z q j) (if j=i then C C' else 0) 0):
    Receiving m u v p i (signFor z z q q G) ((C C'*singleF z q i)+(C C'*singleF z q i)) (C C'*C C'+C C'*C C'):= by
  let f (i:G.ColorIndex):= singleF z q i
  let ℓ j:= if j=i then C (σ:=WebKey G) C' else 0
  have he (j): Receiving m u v p i (f j*f j) (f j*ℓ j+ℓ j*f j) (ℓ j*ℓ j+ℓ j*ℓ j):= by
    have hh:Receiving m u v p i (f j) (ℓ j) 0:=h j
    simpa using hh.mul hh
  have hh:=Receiving.sum Finset.univ _ _ _ fun j _=> he j
  unfold ℓ at hh
  simp only [Finset.sum_add_distrib,mul_ite,ite_mul,ite_true, mul_zero,zero_mul, Finset.sum_ite_eq',Finset.mem_univ] at hh; simpa [signFor, f,mul_comm] using hh

lemma detached {X' Y':E4}(q b:Flavor 0)(R:Web G) {L U L' U':Web G}
    (hR:Receiving m u v p i R 0 0)
    (h₁:Receiving m u v p i (post X' (team G q q)) L U) (h₂:Receiving m u v p i (post Y' (team G b b)) L' U'):
    Flows (fun r=> diff m u v p i r (diff m u v p i r (post X' (team G q q)*post Y' (team G b b)*R)))
      ((post X' (team G q q)*U'+L*L'+(L*L'+U*post Y' (team G b b)))*R):= by simpa using ((h₁.mul h₂).mul hR).twice

lemma transmitted (H:Congruent S m v u) (q b:Flavor 0) (P:Web G) (hP:∀ k∈P.vars,k.1∈S) (hz: WW G (post x (team G q q)*P)=0) (hz': WW G (post y (team G b b)*P)=0)
    : Proves (fun r=> WW G (diff m u v p i r (diff m u v p i r (post x (team G q q)*post y (team G b b)*P))))
      ((8:ℂ)*bilinear (⟨H.raw,H.null_one⟩:Sky m u x) c p q*bilinear (⟨H.raw,H.null_two⟩:Sky m u y) c p b * WW G (singleF x q i*singleF y b i *P)):= by
  let Y₁:= singleF x q i
  let Y₂:= singleF y b i; let A:=team G q q; let B:=team G b b
  let g:=bilinear (⟨H.raw,H.null_one⟩:Sky m u x) c p q; let t:=bilinear (⟨H.raw,H.null_two⟩:Sky m u y) c p b
  have hp := Flows.checks (WW G) (detached p i q b P (grounds p i P H hP) (h₁:=by rw [← signTeam]; exact double_sign p i q (fun j=>from_x c p i j q H)) (h₂:=by rw [← signTeam]; exact double_sign p i b (fun j=>from_y c p i j b H))) -- implicit inferred?
  let a:= C (σ:=WebKey G) g; let c':=C (σ:=WebKey G) t; let r:=a*Y₁; let s:=c'*Y₂
  have he : WW G ((post x A*(c'*c'+c'*c')+(r+r)*(s+s)+((r+r)*(s+s)+(a*a+a*a)*post y B))*P)= _:= (show WW G _ = (8:ℂ)*g*t* WW G (Y₁*Y₂*P) from ?_)
  · rw [← he]; exact hp
  rw [show (post x A * (c'*c'+c'*c')+(r+r)*(s+s)+((r+r)*(s+s)+(a*a+a*a)*post y B))*P= C (2*t*t)*(post x A*P)+C (2*g*g)*(post y B*P)+C (8*g*t)*(Y₁*Y₂*P) from ?_,map_add,map_add, WW_scalar,WW_scalar,WW_scalar]; rotate_left
  · simp [r,s,a,c', _root_.map_ofNat]; ring
  change WW G (_*_)=0 at hz hz'; change WW G (post x A*_)=0 at hz; change WW G (post y B*_)=0 at hz'; rw [hz,hz',mul_zero,mul_zero,add_zero, zero_add]

-- normalize from true zero identity
lemma cascade (H:Congruent S m v u) (P:Web G) (hP:∀ k∈P.vars,k.1∈S) (q b:Flavor 0)
    (hz: WW G (post x (team G q q)*P)=0)(hz': WW G (post y (team G b b)*P)=0)
    (hp:∀ᶠ r:ℝ in atTop, WW G (post (m+r • u) (team G p p)*(post x (team G q q)*post y (team G b b)*P))=0):
    bilinear (⟨H.raw,H.null_one⟩:Sky m u x) c p q*bilinear (⟨H.raw,H.null_two⟩:Sky m u y) c p b * WW G (signFor x y q b G *P)=0:= by
  let K:= post x (team G q q) * post y (team G b b)*P
  have hu : ∀ᶠ r:ℝ in atTop,(∑ i:G.ColorIndex, WW G (diff m u v p i r (diff m u v p i r K)))=0:= by
    filter_upwards [hp] with r hr; change WW G (post _ _*K)=0 at hr; rw [WW_double] at hr
    simp_rw [diff_at,(scrape _ p _).map_smul,map_smul,smul_eq_mul, ← Finset.mul_sum]; rw [hr,mul_zero,mul_zero]
  have hh := (Proves.sum Finset.univ _ _ fun i _=>transmitted c p i H q b P hP hz hz').zero hu
  unfold signFor; rw [Finset.sum_mul,map_sum]; rw [← Finset.mul_sum] at hh; rw [mul_assoc 8, mul_assoc 8] at hh; exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

-- two-covector kernel elimination; replacing terms inductively
structure LocalBill (G:Gauge)(m v:E4)(T:Set E4)(P:Web G): Prop where
  L (q:Flavor 0) : WW G (post (m+v) (team G q q)*P)=0
  R (q:Flavor 0) : WW G (post (m-v) (team G q q)*P)=0
  M (p q b:Flavor 0) (w:E4) : w∉T→ w≠m+v→w≠m-v→ WW G (post w (team G p p)*(post (m+v) (team G q q)*post (m-v) (team G b b)*P))=0

include c in
lemma LocalBill.bilo (B : Finset E4) (P:Web G) (hP :∀ k∈P.vars,k.1∈ B) (hx:x∉B) (hy:y∉B) (h:v≠0) (g : LocalBill G m v B P) (a b : Flavor 0): WW G (signFor x y a b G*P)=0:= by
  obtain ⟨u,H⟩:= joint B m v h hx hy; let X':Sky m u x:=⟨H.raw,H.null_one⟩; let Y': Sky m u y:=⟨H.raw,H.null_two⟩
  obtain ⟨p,hg,Hg⟩:=partner Y' c X' -- order
  let w(t:ℝ):=m+t • u
  have he(V:E4):∀ᶠ r:ℝ in atTop,w r≠V:= (wandering m u V H.raw).mono fun r hr=> sub_ne_zero.mp hr
  let ℓ:= bilinear Y' c p; let z:=bilinear X' c p
  have hv (a b:Flavor 0)(h:z a≠0)(h':ℓ b≠0): WW G (signFor x y a b G*P)=0:= by
    have ht :∀ᶠ r:ℝ in atTop, WW G (post (w r) (team G p p)*(post x (team G a a)*post y (team G b b)*P))=0:= by
      filter_upwards [he x, he y, (eventually_all_finset B).mpr (fun t _=> he t)] with r hi hj ht; exact g.M p a b _ (fun hc=> ht _ hc rfl) hi hj
    exact (mul_eq_zero.mp (cascade c p H P hP a b (g.L a) (g.R b) ht)).resolve_left (mul_ne_zero h h')
  obtain ⟨L,hL⟩:= signForms x y G
  let D:= ((WW G).comp (LinearMap.mulRight ℂ P)).restrictScalars ℝ
  suffices H' : ∀ a b,D (L a b)=0 by rw [← hL]; exact H' _ _
  have hp: ∀ a b,z a≠0→ ℓ b≠0→ D (L a b)=0:= fun a b h h'=> by rw [hL]; exact hv a b h h'
  intro a b
  let S:= (L.compr₂ D)
  apply show (∀ b, S a b=0)→D (L a b)=0 from fun h=>h b
  refine sharpen ℓ (S a) hg (fun b hb=> sharpen z (S.flip b) Hg (fun a ha=>hp a _ ha hb) a)
where sharpen (ℓ f: Flavor 0→ₗ[ℝ] ℂ) (h:ℓ≠0)(H:∀ a,ℓ a≠0→ f a=0)(a): f a=0:= by
        by_cases hh:ℓ a=0; swap; exact H a hh
        obtain ⟨b,hb⟩:=not_forall_not.mp (fun hv=> h (LinearMap.ext fun x'=> not_not.mp (hv x'))); change ℓ b≠0 at hb
        have he:=H (a+b) (by rw [map_add,hh,zero_add]; exact hb); rw [map_add,H b hb,add_zero] at he; exact he
end YM.XSpace.Stab
