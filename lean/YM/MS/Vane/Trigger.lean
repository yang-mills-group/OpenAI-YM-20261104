import YM.MS.Vane.Fee
/-!
# MS UV regulator equivalence estimate for cumulants, including existence. On Mesh horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D: Glade G I}{X:I→ℂ}{d h:ℕ}{ζ:ℝ}
abbrev Δtick (P:Geo I)(i:I): Stem P:= ⟨i,P.θ i, show 0≤_∧ _≤_ from ⟨ P.room i,le_rfl ⟩ ⟩
abbrev rentU (P:Geo I)(t:ℕ)(x:ℝ)(i:I):= ace t x ( inlet ( P:=P ) i )
lemma encode (P:Geo I)(x:ℝ)(d k:ℕ)(i:I): moneyX P (fun _=>x) d k i=(tarB P i)^k * rentU P d x i:= rfl
lemma cost_down (i:I): life P h 0 ζ ( Δtick P i ) = rentU P h ζ i:= by simp [life,rentU, ace] -- δ symbol.Subzero ζ
lemma cost_inter (i:I): ( Gulf P ).price.basic (Δtick P i)=tarB P i:= by change _*(1+|P.θ _|)=_; rw [abs_of_nonneg ( P.room _ )]
lemma cost_gate (i:I): ( West P ).price.basic ( inlet i )=tarB P i:= vested _
lemma far_inlet (i:I): far P h ζ ( inlet i )= rentU P h ζ i:= by unfold far rentU sale; simp [ tstart ] -- inlet unused simp
lemma atmoP (i:I):1≤tarB P i:= by rw [← cost_gate]; exact (West P).price.one_le _
lemma money_nn (i:I): 0≤moneyX P (fun _=>ζ) d h i:= by rw [encode]; exact mul_nonneg (pow_nonneg (zero_le_one.trans ( atmoP (P:=P) i)) _) (( exp_pos _).le)
lemma money_m (hp:d≤ h) (i:I)(k:ℕ): moneyX P (fun _=>ζ) k d i ≤ moneyX P (fun _=>ζ) k h i:= by unfold moneyX; gcongr; exact atmoP i
lemma titel (hx: Here false false ( Gulf P) F ( life P d 0 ζ ))(he: Fed P d ζ H)(hv: Fits false F H): title P ζ d ( blade F ) := by
    obtain hh:= scalar_bill ( K:=Gulf P ) hx; obtain ⟨C,hC,k,hk⟩:= hh; obtain ⟨hp,U,hU,v,hV⟩:= saleable hv he
    refine ⟨ C+U, by linarith,k+v,fun i=>?_⟩; let a (k:ℕ):=moneyX P (fun _=>ζ) d k i; have hl : ‖F i ( P.θ i ) []‖ ≤ C*a k := le_trans ( hk ( Δtick P i ) ) ( le_of_eq (by rw [cost_down,cost_inter,mul_assoc]) ); have hm : ‖blade F i-F i (P.θ i) []‖ ≤ U*a v := le_trans ( hV (inlet (P:=P) i) ) (le_of_eq (by rw [cost_gate,far_inlet,mul_assoc]));
    have hT:= norm_add_le (blade F i - F i (P.θ i) []) ( F i (P.θ i) [] ); rw [sub_add_cancel] at hT; apply le_trans hT
    exact (add_le_add hm hl).trans ( by unfold a; rw [add_mul]; nlinarith [ money_m (P:=P) (ζ:=ζ) (show k≤k+v from (by omega)) i d, money_m (P:=P) (ζ:=ζ) (show v≤ k+v from (by omega)) i d ] ) -- unfold a.T
lemma blade_minus (hx:∀ i,Allow F i)(hv:∀ i,Allow H i)(hu:∀ i,Allow ( F-H ) i): blade ( F-H )= blade F - blade H := funext fun i=> tendsto_nhds_unique (hu i) (( hx i ).sub (hv i))
-- weight univ exported.Packed. Cloud estimate true tails+difference.C.
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
def Verdict (P:Geo I)(h:ℕ)(x:ℝ)(F:Glade G I): Prop:= (∀ i,Allow F i) ∧ paid (West P).price (fun i=> ‖blade F i.1-scalar F i‖ ) (far P h x ) ∧ title P x h ( blade F ) -- internal
variable (h₂:Tour K L P x b B A R)(hx:Tour K' L' P x c B' A' R)
    (M: Arch ( Gulf P ) K L B A R) (M':Arch ( Gulf P ) K' L' B' A' R)(N:Arch (West P) K L B A R)(N': Arch ( West P ) K' L' B' A' R)(Z:ArcS ( Gulf P ) K L K' L' B B' A A' R)(Z':ArcS ( West P ) K L K' L' B B' A A' R)
include h₂ M N
lemma closure (H:Fields x m0 K L B A U)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) 0 ( U S n ):= by
    obtain he:= motion h₂ H hp n; obtain hu:= recall h₂ M N H hp n; obtain ⟨hv,hz⟩:= saleable he hu; have H':= moon h₂ H M hp n|>.1; rw [dotzero] at H'; exact ⟨ hv,hz,titel H' hu he ⟩
include hx M' N' Z Z'
lemma trade (H:Fields x m0 K L B A U) (H': Fields x m0 K' L' B' A' V)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) eps_gain ( U S n-V S n ):= by
   let T:Chase P x m0 R b K L B A U:= ⟨ h₂,H ⟩; let T':Chase P x m0 R c K' L' B' A' V:= ⟨ hx,H' ⟩; obtain hm:= economics T T' Z M M' N N' Z' S hp n; obtain ht:= tokens T T' M M' Z S n hp|>.1; rw [dotzero, ← alter] at ht; have hv:= Fits.subFit ( motion h₂ H hp n ) ( motion hx H' hp n ); obtain ⟨ hU,hW⟩:= saleable hv hm; exact ⟨ hU,hW,titel ht hm hv ⟩
omit h₂ hx M M' N N' Z Z' in
lemma marketV (h₂: Verdict P d 0 F)(he:Verdict P d 0 H)(hu: Verdict P d eps_gain ( F-H )): title P eps_gain d ( blade F-blade H ):= by rw [← blade_minus h₂.1 he.1 hu.1]; exact hu.2.2
-- bulbs specialize real families.
omit h₂ hx M M' N N' Z Z'
open Land Pearl Train Booked Menus Local.Physical
variable { B: Deck G} (V:LitBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(R:W→Label B)(P:Geo I)
abbrev LOrd (V: LitBook B)(P:Geo I)(T:Prescription B)(R: W→Label B)(x:Position W I)(U:Dance G I W):= Fields x m0 (constantP G I ( LowP G )) ( constantP G I ( PlanetL G )) (initials P T) ( rowK V P T ∘ R ) U
abbrev DOrd (Bβ:Booked B) (P:Geo I)(M:MS_Data G Bβ)(R:W→Label B)(x:Position W I)(U:Dance G I W):= Fields x m0 (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) ( rowM P M∘ R ) U
include T
lemma Covers (h:G.Simple)(hx: Mesh P x)(he:TaylorOK M V T): ∃ U V', LOrd V P T R x U ∧ DOrd O P M R x V' ∧ ∀ S: Finset W,S.Nonempty→ ∀ n:ℕ,let k:= charge ( Label.h∘ R ) S; Verdict P k 0 ( U S n ) ∧ Verdict P k 0 ( V' S n ) ∧ Verdict P k eps_gain ( U S n - V' S n ):= by
    obtain ht:= tourist V T hx R h; obtain hV:= builder M hx R; obtain ⟨ U,hU⟩:= formal ht; obtain ⟨W,hW⟩:= formal hV; obtain ⟨Z,X,Tz⟩:= offers V M T R he (gulfG (P:=P)); obtain ⟨Y,Q,RQ⟩:= offers V M T R he ( westV (P:=P) ); exact ⟨ U,W,hU,hW,fun _ hp n=> ⟨ closure ht Z Y hU hp n, closure hV X Q hW hp n,trade ht hV Z X Y Q Tz RQ hU hW hp n⟩ ⟩
end YM.MS.Vane
