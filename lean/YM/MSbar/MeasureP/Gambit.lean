import YM.MSbar.MeasureP.Thorn
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Lattice Gauge Push Uniform
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Whisk RG Precision Next.Free Exterior Laurent Bloch Cane
variable {ι:Type}{G:Gauge}{c n:Side}{g:Ratio c n} {ρ : ℝ} {κ p:ℕ} {η a E D :ℝ}
variable (P : Cross g.count (TypeFace 1) (TypeFace 1))
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "X"=>pension g P G []
local notation "L"=>(g.count.val:ℝ)
variable (x:Primary n G)(v:Primary c G)(h:Cane P D η a E κ p)
local notation "Ψ"=> treasure g G a p
local notation "F"=>yarn g P x
local notation "Θ"=>value a D η E p κ
local notation "w"=> treasure g G a p x
local notation "f"=>Measuring.chart n G
local notation "y"=>Measuring.chart c G
local notation "π"=>swipe y a p
variable (l:List (Primary n G)){k:ℕ}(hk:k≤κ)
include h
lemma woodward (r:List B) : swipe y a p r ≤ (r.map (treasure g G a p x)).prod:=by
    let q(i:A):= f x
    cases r with
    | nil=> unfold swipe Whisk.spread Whisk.zone liftW extent; simp
    | cons v' T=>
       let r : List B:= v'::T; let s: List A:= x::List.replicate T.length x
       have hh:r.length=s.length:= by unfold r s; simp
       refine (tensile g q y a p h.a0 s r hh).trans_eq ?_
       have he:extent (Whisk.zone q ∅ s)=0:= by apply Nat.eq_zero_of_le_zero; apply Whisk.yard; intro i hi j hj
                                                have hx(i)(he: i∈Whisk.zone q ∅ s):i=q x:=by simp only [Whisk.zone,Finset.mem_union,Finset.notMem_empty,false_or,List.mem_toFinset,List.mem_map] at he; obtain ⟨i,hi,rfl⟩:= he; rfl
                                                rw [hx i hi,hx j hj,separation_self]
       rw [he,Nat.cast_zero,zero_div,factor,add_zero,mul_zero,Real.exp_zero,one_pow,one_mul,one_mul]
       change beads (fun (_:A)(j:B)=> w j) s r= (r.map w).prod
       have hp(s:List A)(r:List B)(h:r.length=s.length) : beads (fun (_:A)(j:B)=> w j) s r= (r.map w).prod:=by
           induction s generalizing r with
           | nil=> rw [show r=[] by simpa using h]; rfl
           | cons a l ih=> cases r with |nil=>simp at h | cons j t=> rw [beads,List.map_cons,List.prod_cons]; congr 1; exact ih _ (by simpa using h)
       exact hp s r hh
lemma capR (x:A) : (∑ j:B,treasure g G a p x j*|pension g P G [] x j|) ≤ Θ/L :=by
    apply (crown g P x (h.res [] (by simp)) h.room h.a0 (zero_le_one.trans h.E0) h.sufficient).trans; simp only [List.length_nil,add_zero,pow_one]; rw [← mul_div_assoc,← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity)
    apply le_trans _ (le_mul_of_one_le_left (tot P h) (jaws _))
    let R:=factor a p (2*4); have he:1≤R:= (inc p h.a0 le_rfl (by norm_num)|>.trans' (show (1:ℝ) ≤ factor a p 0 from by simp [factor]))
    have hp:0 ≤ E:=zero_le_one.trans h.E0; have hh:=h.D0
    unfold candle;
    exact le_mul_of_one_le_left (by positivity) he
lemma capC (j:B) : (∑ x:A,treasure g G a p x j*|pension g P G [] x j|) ≤ L^4*(Θ/L) :=by
    apply (coin g P j (h.res [] (by simp)) h.room h.a0 (zero_le_one.trans h.E0) h.sufficient).trans
    refine mul_le_mul_of_nonneg_left ?_ (by positivity); simp only [List.length_nil,add_zero,pow_one]; rw [← mul_div_assoc,←mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); have hp:=h.D0; have ht:0≤E:=zero_le_one.trans h.E0; apply (le_mul_of_one_le_left (by positivity : (0:ℝ) ≤ E*Real.exp η*(Fintype.card (TypeFace 1)*D)) (show 1≤ factor a p (2*4) from (inc p h.a0 (x:=0) le_rfl (by norm_num)|>.trans' (by simp [factor])))).trans (le_mul_of_one_le_left (tot P h) (jaws _))
noncomputable def feed(a η E D:ℝ)(p κ n:ℕ):= (2*((κ:ℝ)+1)* value a D η E p κ)^n
local notation "𝔅"=> feed a η E D p κ l.length
local notation "I" =>Ψ x v*|X x v|
variable {b:ℝ}(hb:a/(g.count.val:ℝ) ≤ b)(hp:k≤p)
noncomputable def mos (g:Ratio c n)(P:Cross g.count (TypeFace 1) (TypeFace 1))(x:Primary n G)(v:Primary c G)(m:ℕ)(l:List (Primary n G))(T: List (Primary c G)):= pension g P G [] x v*arco (yarn g P x) m l T -- notation
local notation "U"=> fun T=> beads X (x::l) (v::T)-mos g P x v k l T
include hb hk hp
lemma mantle : delta x l g^k ≤ (4/L)^k*swipe f b p (x::l) :=by
    let z:=dim (x::l); have he:0≤b:= (div_nonneg h.a0 (by positivity)).trans hb
    unfold delta; calc
       _ ≤ ((4/L)*(1+(z:ℝ)))^k:=by refine pow_le_pow_left₀ (by positivity) ?_ k; rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ (by positivity); change _ + 4*(z:ℝ) ≤ _; linarith
       _ ≤ _:=by rw [mul_pow]; refine mul_le_mul_of_nonneg_left ?_ (by positivity); change (1+(z:ℝ))^k≤factor b p z; exact (pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) z]) hp).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
lemma potion (J:List B →ℝ) (hJ:Yarn l.length (fun T=> (T.map (treasure g G a p x)).prod*|J T|) ≤ (2*((κ:ℝ)+1)*(Θ/L))^l.length*delta x l g^k) : Yarn l.length (fun T:List B=> swipe y a p (v::T)*|pension g P G [] x v*J T|)≤ I*(𝔅/L^l.length)*((4/L)^k*swipe f b p (x::l)):=by
    have h0:0≤I:= mul_nonneg (grot_positive ..|>.le) (abs_nonneg _); have he:=specs P h
    calc
       _ ≤ I*Yarn l.length (fun T=> (T.map w).prod*|J T|):=by rw [←sheen]; refine shiny _ fun T _=>?_ ; exact (mul_le_mul_of_nonneg_right (woodward P x h (v::T)) (abs_nonneg _)).trans_eq (by rw [List.map_cons,List.prod_cons,abs_mul]; ring)
       _ ≤ I*((2*((κ:ℝ)+1)*(Θ/L))^l.length*delta x l g^k):=mul_le_mul_of_nonneg_left hJ h0
       _ ≤ _:=by rw [←mul_assoc (Ψ _ _ * _), ←mul_div_assoc,div_pow]; refine mul_le_mul_of_nonneg_left (mantle P x h l hk hb hp) ?_; exact mul_nonneg h0 (by positivity)
lemma topped (he:0<k)(ht:g.count.val ≤ dim (x::l)): Yarn l.length (fun T=> swipe y a p (v::T)*|mos g P x v k l T|) ≤ I*(𝔅/L^l.length)*((4/L)^k*swipe f b p (x::l)) :=by
    apply potion P x v h l hk hb hp (arco F k l); change Yarn _ _ ≤ _; apply (highland P x h l hk he ht).trans; have hx:=specs P h
    refine mul_le_mul_of_nonneg_right ?_ (by unfold delta; positivity)
    gcongr; linarith only [Nat.cast_nonneg (α:=ℝ) κ]
lemma fern (he:dim (x::l) ≤ g.count.val) : Yarn l.length (fun T=> swipe y a p (v::T)*|U T|)≤ I*(𝔅/L^l.length)*((4/L)^k*swipe f b p (x::l)):=by
   refine le_trans (le_of_eq (stitch l.length ?_)) (potion P x v h l hk hb hp _ (conifers P x h l hk he)); intro T _; simp [beads,mos,mul_sub]
lemma treeTop (he:L≥2)(ht:g.count.val ≤ dim (x::l)) : Yarn l.length (fun T:List B=> swipe y a p (v::T)*|beads X (x::l) (v::T)|) ≤ I*(𝔅/L^l.length)*((4/L)^k*swipe f b p (x::l)) :=by
    let W:=swipe f b p (x::l); have hw:0≤ W:= effect ..|>.le; have hi:0≤I:=mul_nonneg (grot_positive ..|>.le) (abs_nonneg _); have hx:=specs P h; have hz :0 ≤ Θ/L:=by positivity
    have hr: (2/L)^p ≤ (4/L)^k:=by apply (pow_le_pow_of_le_one (by positivity : (0:ℝ) ≤ 2/L) (div_le_one (by positivity)|>.mpr he) hp).trans; gcongr; norm_num
    refine (hold g f y X h.a0 hz (fun x=> capR P h x) x v l (cutdown g hb ht)).trans ?_; change ((2/L)^p*W)*I*(Θ/L)^l.length ≤ _
    have hp : Θ^l.length ≤𝔅:= by apply pow_le_pow_left₀ hx _; apply le_mul_of_one_le_left hx; linarith only [Nat.cast_nonneg (α:=ℝ) κ]
    calc
      _ = (I*(Θ^l.length/L^l.length))*((2/L)^p*W):=by rw [div_pow]; ring
      _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp (by positivity)) hi) (mul_le_mul_of_nonneg_right hr hw) (by positivity) (mul_nonneg hi (div_nonneg ((pow_nonneg hx _).trans hp) (by positivity)))
lemma grand(hK:0 < k)(he:L≥2) : Yarn l.length (fun T=>swipe y a p (v::T)*|U T|) ≤2*(I*(𝔅/L^l.length)*((4/L)^k*swipe f b p (x::l))):=by
    by_cases hz:dim (x::l) ≤ g.count.val
    · have ht:= fern P x v h l hk hb hp hz; apply ht.trans; apply le_mul_of_one_le_left _ one_le_two; exact le_trans (luster l.length (fun i hi=> mul_nonneg (effect ..|>.le) (abs_nonneg _))) ht
    rw [two_mul]; refine le_trans ?_ (add_le_add (treeTop P x v h l hk hb hp he (by omega)) (topped P x v h l hk hb hp hK (by omega))); rw [← pockets]; refine shiny _ fun T h=>?_ ; rw [←mul_add]; exact mul_le_mul_of_nonneg_left (abs_sub ..) (effect ..|>.le)
end YM.MSbar.Measuring
