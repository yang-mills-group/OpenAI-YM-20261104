import YM.AllOrder.Catch.Line
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch.Clock
open Function Filter Matrix Metric MeasureTheory
open scoped Topology Classical
variable {X α:Type*} {Z:X→Type*} 
variable (S:Clock X) {Y:Type*}(Q:Clock Y) (u:Y→X) {f g:X→ℝ}{a b C:ℝ}
local notation "H"=> S.Meter
abbrev Quite (S:Clock X) (f:X→ℝ):= ∃ a:ℝ,S.Meter f a
def Stretch (S:Clock X)(v:X→ℝ)(h:∀ᶠ i in S.rail,1≤ v i): Clock X:= ⟨S.rail,fun i=>S.cost i * v i,tendsto_atTop_mono' _ (by filter_upwards [S.positive,h] with i hi hp; exact le_mul_of_one_le_right hi.le hp) S.drive⟩
lemma grow {S:Clock X} {s:X→ℝ}(h: S.Meter f a)(he:∀ᶠ i in S.rail,1≤ s i)(hp:0 ≤ a): (Stretch S s he).Meter f a:= by
 intro b hb; filter_upwards [h b hb,S.positive,he] with i hi hI hs; exact hi.trans (Real.rpow_le_rpow hI.le (le_mul_of_one_le_right hI.le hs) (hp.trans hb.le))
section pace
variable (Z:X→Type*)[∀ i,NormedAddCommGroup (Z i)]
local notation "P"=> S.stage Z
def tier (S:Clock X) : Clock (Sigma Z) := Stretch (S.stage Z) (fun i=>1+‖i.2‖) (Eventually.of_forall fun i=> le_add_of_nonneg_right (norm_nonneg _))
local notation "P₀"=> tier Z S
lemma windy : (P₀).Meter (fun v=> ‖v.2‖) 1:= by

 apply Meter.pay; filter_upwards [(P).pos] with i hi; change  |‖i.2‖| ≤ (S.cost i.1 *(1+‖i.2‖))^(1:ℝ); rw [abs_of_nonneg (norm_nonneg _),Real.rpow_one]; exact (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_left (by positivity) hi)
end pace
variable {S}
namespace Quite
lemma monotone (h:S.Quite f)(he:∀ᶠ i in S.rail,|g i|≤|f i|): S.Quite g:=by obtain ⟨p,hp⟩:=h; exact ⟨p,hp.smaller he⟩
lemma travel (h:S.Quite f)(u:Y→X)(hp:S.Fare (U:=Q) u): Q.Quite (f ∘ u):=by obtain ⟨p,hp'⟩:=h; exact ⟨p,hp'.pays u hp⟩
lemma widen (h:S.Quite f)(s:X→ℝ)(he:∀ᶠ i in S.rail,1≤s i): (Stretch S s he).Quite f:=by obtain ⟨p,hp⟩:=h; exact ⟨max p 0,grow (hp.weak (le_max_left ..)) he (le_max_right ..)⟩
lemma add (h:S.Quite f)(hG:S.Quite g): S.Quite (fun i=>f i+g i):=by obtain ⟨p,hp⟩:=h; obtain ⟨q,hq⟩:=hG; exact ⟨max p q,(hp.weak (le_max_left ..)).add (hq.weak (le_max_right ..))⟩
lemma mul (h:S.Quite f)(hG:S.Quite g): S.Quite (fun i=>f i*g i):=by obtain ⟨p,hp⟩:=h; obtain ⟨q,hq⟩:=hG; exact ⟨_,hp.mul hq⟩
lemma c (S:Clock X)(a:ℝ): S.Quite (fun _=>a):=⟨_,Meter.const S a⟩
lemma pow (h:S.Quite f)(k:ℕ): S.Quite (fun i=> f i^k):= by obtain ⟨p,hp⟩:=h; exact ⟨_,hp.pow k⟩
lemma neg (h:S.Quite f): S.Quite (fun i=> -f i):=by obtain ⟨p,hp⟩:=h; exact ⟨p,hp.neg⟩
lemma bound (h:S.Quite f): ∃ n:ℕ, ∀ᶠ i in S.rail, |f i| ≤(S.cost i)^n := by obtain ⟨p,hp⟩:=h; obtain ⟨n,h⟩:= exists_nat_gt p; exact ⟨n,by simpa only [Real.rpow_natCast] using hp n h⟩
lemma tier_bound [∀ i,NormedAddCommGroup (Z i)](f:Sigma Z→ℝ)(h: (tier Z S).Quite f):∃ n:ℕ,∀ᶠ i in S.rail,∀ j:Z i,|f ⟨i,j⟩|≤ S.cost i^n*(1+‖j‖)^n:= by
 obtain ⟨n,hp⟩:= Quite.bound h; refine ⟨n, S.everybody (V:=Z) (fun z=> |f z|≤S.cost z.1^n*(1+‖z.2‖)^n) |>.mp ?_⟩; filter_upwards [hp] with i hi; rw [← mul_pow]; exact hi
end Quite
-- Bring back via morphism after spin
lemma domestic {γ:X→ℝ}
    (h:H γ a):S.Quite γ:= Exists.intro _ h
-- B-sharp inverse estimate and sum F.Mark.V.Basic flux
variable {u}
lemma Meter.rises (h:∀ᶠ i in S.rail, S.cost i ≤ f i)(ht:0≤a):Tendsto f S.rail atTop:= tendsto_atTop_mono' _ h S.drive
lemma booker {i:X→Y}(hf:Tendsto i S.rail Q.rail){V:Y→Type*}{s:∀ i,Set (V i)}(j:X→Sigma V)(he:∀ x, (j x).1=i x)(h:∀ᶠ x in S.rail, (j x).2∈ s (j x).1)
   (p₀:(y:Y)→V y→Prop)(hh:∀ᶠ y in Q.rail,∀ x∈s y, p₀ y x): ∀ᶠ x in S.rail,p₀ (j x).1 (j x).2:=by
 have ht:Tendsto (Sigma.fst∘ j) S.rail Q.rail:= hf.congr (fun i=> (he i).symm); filter_upwards [ht.eventually hh,h] with i hi he; exact hi _ he
end YM.AllOrder.Catch.Clock
