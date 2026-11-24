import YM.MSbar.Cypress.RareV
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Cypress
open YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
open Lapaz
variable {G:Gauge}{c f:Side} {S:StepData c f}(F:Forest S.ratio)(R:Rep G f)(v:S.Choices)(J:Voice G)(Q:Palisade)(χ:ChartRatio G)
local notation "V"=>Primary c G
local notation "P0"=>Key F G
local notation "G!"=>Joint F G
local notation "T"=>Positions (Joint F G)
local notation "x!"=> Positions (Primary c G)
local notation "Ω"=> address F G
local notation "H"=>mold R F v
variable (X Y:Support f)(U':Config G f) (t:ℝ)(Z:Positions (Primary c G))
local notation "Λ"=> includeX (G:=G) F X
local notation "X₀"=>SpaceP F X G
local notation "χ!"=>(pinch (includeX (G:=G) F X) H)⁻¹
variable (e:PathData G)(l:Clip)(ρ:fieldDir G c 1→ AxisChart G F)
local notation "ν"=>vest (priced F v R.clip R.path) (t • Z)
local notation "f1"=>linCash F (t • Z)
open Next.SectorChange
local notation "I!"=>hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "r₀"=>rental F J R Y v (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "c!"=> sampleY F R v J X Y U' (t • Z)
local notation "A!"=> berth F R v J X Y U' Z t
variable {A B d C P D K w E:ℝ} (h:Suite J χ F X Y (postcard G c t Z) v R (vest (priced F v R.clip R.path) (t • Z)) A B d C P D (linCash F (t •Z)))
variable {a b r D0 d' d0 c' U w' :ℝ} {n p m j N:ℕ}
local notation "α!"=>Rolling.straight F G
local notation "Q'"=> includeX (G:=G) F X
variable (z:Site f)
variable (T':Nesting G f)(g:ℝ→ℝ)(s:Site f→ G.Color)
local notation "P!"=>pegged F s (film R T' t p ∘ Lodge.Clamp g)
local notation "τ'"=> poring F ρ
local notation "φ'"=> center F ρ
local notation "Γ"=> H⁻¹
local notation "Q₀"=> (0:Positions (Key F G))
local notation "c'₁"=> Cacao.growP
local notation "a'"=> barbed F v χ T'
local notation "α₀"=>ink c l e
local notation "b'"=>stampD F v G
local notation "ι!"=> hands F G
variable (L':List (Primary c G))(hk:Kind T')(hp:Critical F R.clip R.path ρ) (hd:ClassicalMatch F R.clip l R.path e ρ) (hξ:LocalRatio χ)(hK:(mold R F v).PosDef)(hw:Premier (Rolling.main f R.clip R.path))(he:S.patch.Branches S.kernel G)
local notation "Ω'"=> blastP F R v χ t e l ρ T' g p L' s
local notation "Φ'"=> song F v R.path R.clip χ T' ρ
include hk hp hd hξ hK he hw
variable {T0 t1 t2 t3 t4 t5 ε U0 W0:ℝ}(hr:R.Lawful t1 t2 t3 t4 t5) (hR:∀ i, 0<R.eval i)(hF:Reef (pegged F s (film R T' t p ∘ Lodge.Clamp g)) 1)
local notation "τv'"=> PPress S R.beta t R
-- avoid notation conflict.
local notation "Kρ"=> H⁻¹
local notation "χ0"=> PowerSeries.coeff
include hr hR hF
variable (S':Rep G c) (hS:S.push R.beta R.eval=S'.eval)(hg:S'.clip=l)(hQ:S'.path=e)
local notation "W'"=>colorCut F v R.path R.clip χ T' ρ
local notation "X!"=> (Positions (Primary c G)→ℝ)
local notation "P'"=> film S' W' t p
include hg hQ hS
omit hk hp hd hξ hK hw hF
lemma splice : logK (PPress S R.beta t R)= fun x=> Real.log (nut S R.beta G)+vine S' t x :=by
    let W:=PPress S R.beta t R; let K(v:x!) := postcard G c t v; have he'(x): PPress S R.beta t R x=nut S R.beta G*S'.eval (palace (t • x)):=by rw [prec R.beta t x he R t1 t2 t3 t4 t5 hr hR,hS]; congr; -- defeq? placement
    funext x; unfold logK Aqua.vine walnut; have ht:0<W x:= Tonic.base R.beta t x he R t1 t2 t3 t4 t5 hr hR; have hx:0< nut S R.beta G:=nut_pos ..
    rw [he']; apply Real.log_mul hx.ne'; intro ho; rw [show W _=_ from he' x,ho,mul_zero] at ht; exact lt_irrefl _ ht
section
omit hS hg hQ hr hR he
variable {σ :Type}[Fintype σ]
lemma nillC (i:ℕ)(l:List σ)(x:Positions σ)(h:l≠[])(c:ℝ):buoy (fun _=>c) x l=0:=by
     classical
     rw [budP _ l l.length x contDiffAt_const le_rfl,glance_read l (show ContDiffAt ℝ (↑l.length) (fun _ : Positions σ=>c) x from contDiffAt_const) le_rfl,iteratedFDeriv_const_of_ne (𝕜:=ℝ) (show l.length≠0 from by simpa using h) c]; rfl
lemma remove (i:ℕ)(l:List σ)(x:Positions σ)(f g:Positions σ→ℝ)(h:ContDiffAt ℝ i f x)(he:ContDiffAt ℝ i g x)(ht:l.length ≤ i): buoy (f-g) x l=buoy f x l-buoy g x l:=by
    rw [sub_eq_add_neg]; unfold buoy; rw [Lis.addedL i (l.map Uniform.bolt) f (-g) h he.neg (by rw [List.length_map]; exact ht),← neg_one_smul ℝ g]; change _+roc (fun x=>(-1:ℝ)*g x) _ _= _; rw [Lis.wed i _ _ _ he (by rw [List.length_map]; exact ht)]; ring
end
local notation "π"=> PowerSeries.coeff
omit hS hr hR he
lemma flowP (i:ℕ)(hL:L'≠[]) : π i (fleet Φ' α₀ Z L')= buoy (atlas W' p i S'.path S'.clip) Z L':=by
      rw [hg,hQ];
      let k' := π i Φ'; let F':= fun x:x!=> eval x (π i (Φ'-PowerSeries.C α₀)); let G':= fun x:x!=>eval (0:x!) k'; have hh(i):ContDiffAt ℝ (↑(i:ℕ)) F' Z:=(vent ..).contDiffAt.of_le le_top
      rw [Duel.extras]; change buoy F' _ _=_; rw [show atlas (W') p i e l= F'-G' from ?_,remove L'.length L' Z F' G' (hh L'.length) contDiffAt_const le_rfl, nillC 0 _ _ hL,sub_zero]
      funext z; unfold Lis.atlas; change eval z (π i (tariff c p _ _ _))= F' z-G' z; unfold tariff F' G' colorCut Rewind; rw [_root_.map_sub,_root_.map_sub,PowerSeries.coeff_mk, Bakery.rewind,map_sub, map_sub,map_sub,eval_C]; unfold k'; ring
include hS hr hR he
lemma cropR (hL:L'≠[]) : buoy (film S' W' t p) Z L'= buoy (logK (PPress S R.beta t R)) Z L'- taste p (fleet Φ' α₀ Z L') t:=by
     let S₀:= Real.log (nut S R.beta G); let U:= logK (PPress S R.beta t R); let V':= vine S' t; let k:= L'.length; let g(x:x!):= S₀; let G':=ore S' W' t p; have hv:V'=U-g:=by
          refine eq_sub_of_add_eq ?_; funext i; exact (add_comm _ _).trans (congr_fun (splice (S:=S) R t e l he hr hR S' hS hg hQ) i|>.symm)
     have hU:ContDiff ℝ (↑k) U:= (Tonic.curvet R.beta t he R t1 t2 t3 t4 t5 hr k).log (fun i=> (Tonic.base R.beta t i he R t1 t2 t3 t4 t5 hr hR).ne'); -- args
     unfold film; rw [remove k L' Z V' G' (by rw [hv]; exact hU.contDiffAt.sub contDiffAt_const) ((Aqua.pure ..).contDiffAt.of_le le_top) le_rfl,hv, remove k L' Z U g hU.contDiffAt contDiffAt_const le_rfl, nillC 0 L' Z hL, sub_zero]; congr 1
     unfold G' ore taste; simp_rw [show ∀ i,PowerSeries.coeff i (fleet Φ' α₀ Z L')= _ from fun i=> flowP (p:=p) F R v χ Z e l ρ T' L' S' hg hQ i hL]; let Vx(v:ℕ):= atlas W' p v S'.path S'.clip
     suffices Hx:∀ i:ℕ,buoy (fun x=>∑ j∈range i,t^j*Vx j x) Z L'= ∑ j∈range i,t^j*buoy (Vx j) Z L' from Hx _
     intro i; have ht(i:ℕ):ContDiffAt ℝ (↑k) (Vx i) Z:= (vent ..).contDiffAt.of_le le_top; induction i with
     | zero=> simp only [range_zero,sum_empty]; exact nillC 0 L' Z hL _
     | succ i ih=>
         simp_rw [Finset.sum_range_succ]; let g(x:x!):= ∑ j∈range i,t^j*Vx j x; let h(x:x!):= t^i * Vx i x; change roc (g+h) _ _=_; rw [Lis.addedL L'.length _ _ _ (show ContDiffAt ℝ L'.length g Z from ContDiffAt.sum (fun j _=> (ht j).const_smul (t^j))) (show ContDiffAt ℝ L'.length h Z from (ht i).const_smul (t^i)) (by simp)]; congr 1; exact Lis.wed k _ _ _ (ht i) (by rw [List.length_map]) -- indentation
end YM.MSbar.Cypress
