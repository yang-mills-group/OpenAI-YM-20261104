import YM.SignedWilsonExpansion.PairWave
namespace YM.SignedWilsonExpansion.Contrast
/-! # Homothetically paired MARK reading, energy on plane, from theory arrays
    after own comparison removal. Face-replacement test bookkeeping shared
    with commissioning. The nonlinear F3-Rose algebra on the correct arrays at
    BOTH placements, with homothety made visible. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace PhaseTilt
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {O:Booked (Press.portDeck G)}(M:MS_Data G O) (ν:ℝ) {n:ℕ}
local notation "θ" => Fin 3
local notation "Q" => PowerSeries ℂ
local notation "d" => (Finset (Fin 3))
local notation "g'" => Sec G 4
local notation "Ξ" => PowerSeries.coeff
local notation "Φ" => Manifest.response
local notation "η" => Facets.posing
local notation "κ" => Extent.token
local notation "E" => lens G
local notation "Ω" => leaf G 4
local notation "W" => (Finset.univ (α:=θ))
local notation "λQ" => Equator.iris -- parser
local notation "N" => Fintype.card G.ColorIndex
variable (x:Stage 3)(F H:Way G 4)(p:Tags G 4 n)
abbrev testE (G:Gauge)(n:ℕ) : Tags G 4 n:= fun _=> lens G
abbrev maskE (G:Gauge)(a:Finset (Fin 3)):= Rose.missing (testE G 3) a
abbrev spectrum (F:Way G 4)(x:Stage 3)(s: d ):= Reg.Point.story (F 3 x) (maskE G s)
def track (F:Way G 4)(x:Stage 3): Q:= Rose.b3 (spectrum F x)
-- cyclic shift on Fin 3. no orientation average or projection of colors here
abbrev K0 (i:Fin 3): Finset (Fin 3):= Finset.univ.erase i
variable (a:θ)
local notation "i₀" => (3:Idx)
local notation "j" => (a+1)
local notation "k" => (a+2)
lemma card_pair : K0 a={a+1,a+2}:= (by decide :∀ a: Fin 3,K0 a={a+1,a+2}) a
lemma beforeP (V:Way G 4)(h:StarGround V)(s:Finset θ): Ξ 0 ( spectrum V x s )=iris x (maskE G s):= by rw [spectrum, Reg.Point.story,PowerSeries.coeff_mk,h]
lemma mask_one (a:θ): maskE G {a}=update (fun _=> leaf G 4) a E:= by funext i; by_cases h:i=a <;> simp [maskE,testE,Rose.missing,h]
lemma mask2 : maskE G (K0 a)= update ( update (fun _=>Ω) (a+2) E ) (a+1) E:= by funext i; rw [card_pair]; fin_cases a <;> fin_cases i <;> (first| rfl| simp [maskE,testE,Rose.missing,Fin.isValue,update]); -- rotation arithmetic
lemma mask3 : maskE G ( Finset.univ )=testE G 3:= by funext i; simp [maskE,testE,Rose.missing]
-- moment.price formulas
abbrev coin (x:Stage 3)(i:Fin 3):= oneOnly (G:=G) x i ∘ₗ coeS 4
abbrev triple (x:Stage 3)(i:Fin 3):= journey x i (i+1) (i+2) (lens G).val (lens G).val ∘ₗ coeS 4
abbrev dab (x:Stage 3)(i:Fin 3):ℂ:= iris x ( maskE G ( K0 i ) )
local notation "u0" => testE G 3
def Xi (G:Gauge) (x:Stage 3): Sec G 4→ₗ[ℂ] ℂ:= ∑ i:Fin 3,( triple x i - dab (G:=G) x i • coin x i )
local notation "X" => Xi G
variable (y: Sec G 4)
lemma iris_one : iris x ( update (fun _=> leaf G 4) a y )= coin x a y:= by
     apply congr_arg (moment G x.val); funext i; by_cases H:i=a; · subst i; simp only [update_self]
     simp only [update_of_ne H]; rfl
lemma unval {w:Tags G 4 n}(i:Fin n)(p:Sec G 4) : coeS 4 ∘ update w i p=update (coeS 4 ∘ w) i (coeS 4 p):= by funext l; by_cases he:l=i <;> simp [he]
lemma iris2 : dab (G:=G) x a=dyad x j k (E).val (E).val := by
    unfold dab; rw [ mask2 ]; change moment G x.val (coeS 4∘ update _ _ _)=_; rw [unval, unval]; rfl -- rewrite under comp?
lemma iris3 : iris x (update u0 a y)=triple x a y:= by
    unfold iris scene triple journey; rw [ LinearMap.comp_apply,MultilinearMap.toLinearMap_apply ]; apply congr_arg (moment G x.val); funext i; fin_cases a <;> fin_cases i <;> rfl
lemma iris_price : iris x (maskE G {a})=0:= by rw [ mask_one,iris_one ]; exact single_off (G:=G) x a 3 3
lemma iris_lens (h:Holds x): iris x (testE G 3)= ↑( (N*8* pay x 0 1* pay x 0 2* pay x 1 2:ℝ) ):= by rw [← show update u0 0 E=u0 from Function.update_eq_self .., iris3 ]; let i:θ:=0; change journey x 0 1 2 (E).val (E).val (E).val=_; rw [ tri_bill x 0 1 2 (by decide) (by decide) (by decide) h ]; simp only [ bitT, ↓reduceIte, one_mul ]
lemma bell_unit : X x (leaf G 4)=0:= by
    rw [Xi,LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro i _; rw [ LinearMap.sub_apply, LinearMap.smul_apply ]; change journey x i (i+1) (i+2) (E).val (E).val (1:WickPol G)- dab (G:=G) x i • oneOnly x i (1:WickPol G)=0; have hp(i:θ): i≠ i+1∧ i≠i+2:=(by fin_cases i <;> decide); rw [ WickFace.dropJ x (E).val (E).val _ _ _ (hp i|>.1) (hp i|>.2),coinS, iris2 ]; simp
section pay2
-- usable point differences for fitted field and also for scale law
variable {F H x} {Z:Guard G 4}
local notation "Θ" => spectrum
abbrev ticket (F:Way G 4)(x:Stage 3):= Rose.b3 (spectrum F x)
def clip2 (P:Structure1.Point G 4 3)(x:Stage 3):ℂ:= P (testE G 3)-∑ a:Fin 3,dab (G:=G) x a * P ( maskE G {a} )
lemma fee0 (hg:StarGround F): Ξ 0 (track F x)=iris x (testE G 3):= by
   unfold track Rose.b3; rw [ PowerSeries.coeff_zero_eq_constantCoeff_apply ]; simp only [two_smul,map_add,map_mul,map_sub, ← PowerSeries.coeff_zero_eq_constantCoeff_apply ];
   simp_rw [ beforeP x F hg, iris_price, mask3 ]; ring
lemma fee1 (hf:F 3 x 1=0): Ξ 1 ( track F x )=0:= by
   have he(s:d): Ξ 1 ( spectrum F x s )=0:= by rw [spectrum,Reg.Point.story, PowerSeries.coeff_mk,hf]; rfl
   unfold track Rose.b3; simp only [map_add,map_sub,map_smul,PowerSeries.coeff_one_mul, he, mul_zero, zero_mul, add_zero, sub_zero, smul_zero]
lemma fee2 (hg:StarGround F)(hf:F 3 x 1=0): Ξ 2 ( track F x )=clip2 (F 3 x 2) x:= by
   let K:= spectrum F x; have he(s:d): Ξ 1 (K s)=0:= by unfold K spectrum; rw [ Reg.Point.story, PowerSeries.coeff_mk,hf ]; rfl
   have hv(a:Fin 3): Ξ 0 (K {a})=0:= (beforeP x F hg _).trans ( iris_price .. )
   have ht (a:Fin 3): Ξ 2 (K (K0 a)*K {a})=dab (G:=G) x a*(F 3 x 2 ( maskE G {a} )):= by rw [PowerSeries.coeff_mul, show Finset.antidiagonal 2={(0,2),(1,1),(2,0)} from by decide,sum_insert (by decide),sum_insert (by decide),sum_singleton ]; simp only [ he,hv,mul_zero,add_zero,K,spectrum,Reg.Point.story,PowerSeries.coeff_mk,hg 3 x ] -- check
   have hK:Ξ 2 ( (2:ℂ) • (K {0}*K {1}*K {2}) )=0:= by rw [map_smul]; suffices h: Ξ 2 ( K {0}*K {1}*K {2})=0 from ( by rw [h,smul_zero] ); rw [ PowerSeries.coeff_mul, show Finset.antidiagonal 2={(0,2),(1,1),(2,0)} from by decide,sum_insert (by decide),sum_insert (by decide),sum_singleton ]; simp only [ he,hv,add_zero, mul_zero ]; simp_rw [ PowerSeries.coeff_zero_eq_constantCoeff_apply ] at hv ⊢; rw [ map_mul, hv, zero_mul,zero_mul ]
   unfold track Rose.b3; simp only [ map_add, map_sub ]; rw [ hK ];
   unfold clip2; rw [show ({0,1}: Finset θ)= K0 2 from by decide,show ({1,2}:Finset θ)=K0 0 from by decide, show ({0,2}:Finset θ)=K0 1 from by decide ]; rw [ ht,ht,ht, add_zero, spectrum, Reg.Point.story,PowerSeries.coeff_mk, mask3, Fin.sum_univ_three ]; abel
lemma second_gap (hf:StarGround F) (hg:StarGround H) (hF:F 3 x 1=0)(hH:H 3 x 1=0)(hz:Base Z)(s:∀ p,F 3 x 2 p-H 3 x 2 p=Φ x p (Ξ 2 Z)):
    Ξ 2 ( track F x )-Ξ 2 ( track H x )= X x ((Ξ 2 Z) E):= by
   rw [ fee2 hf hF, fee2 hg hH ]; unfold clip2;
   have hp : Φ x u0 (Ξ 2 Z)=∑ a:Fin 3,triple x a ( ( Ξ 2 Z ) E ):= by change (∑ i:θ,iris x ( update u0 i ((Ξ 2 Z) E) ))=_; exact Finset.sum_congr rfl (fun i _=> (iris3 x i ( (Ξ 2 Z) E )))
   have he(i:Fin 3): Φ x (maskE G {i}) (Ξ 2 Z)= coin x i (( Ξ 2 Z ) E):= by
       unfold Manifest.response; rw [ mask_one ]; change (∑ i':θ,iris x ( update (update (fun _=>Ω) i E) i' ((Ξ 2 Z) (update (fun _=>Ω) i E i')) ))=_; rw [ Finset.sum_eq_single_of_mem i (mem_univ _) ]; · rw [update_self,update_idem,iris_one]
       intro b _ hb; rw [update_of_ne hb]; rw [ show ( Ξ 2 Z ) (Ω)=0 from (hz.high 2 (by decide)).1 ]; apply MultilinearMap.map_coord_zero _ _ (update_self ..)
   rw [ sub_sub_sub_comm, s ]; unfold Xi; rw [ hp, ← Finset.sum_sub_distrib, LinearMap.sum_apply, ← Finset.sum_sub_distrib ]; apply Finset.sum_congr rfl; intro i _; rw [ LinearMap.sub_apply, LinearMap.smul_apply,← mul_sub,s,he ]; rfl
end pay2
section scale
variable (t:ℝ)
local notation "p'" => η t x
lemma scales (s:d) :
     spectrum (scaling t F) x s=(κ t (s.card*4)) • spectrum F (η t x) s:= by
   unfold spectrum; let v:= maskE G s; refine PowerSeries.ext fun u=> ?_
   let a (i:θ):= κ t ( if i∈s then 4 else 0 ); have hz : Level.Dial 4 t ∘ v=fun i:θ=> a i • v i:= by
       funext i; by_cases hi:i∈s; · simp only [Function.comp_apply,v, maskE, a, Rose.missing, if_pos hi, testE]; exact money (G:=G) t 3 3
       simp only [comp_apply,v, maskE,a,Rose.missing,if_neg hi]; exact (unit_dial (G:=G) t).trans (one_smul ℂ ( leaf G 4 )).symm
   rw [ map_smul ]; unfold Reg.Point.story; simp_rw [ PowerSeries.coeff_mk,Facets.scale_at ]; change F 3 (η t x) u ( Level.Dial 4 t ∘ v )=_; rw [hz, MultilinearMap.map_smul_univ]; unfold a Extent.token; rw [ Finset.prod_pow_eq_pow_sum ]; congr 2; rw [ Finset.sum_ite_mem ]; simp
lemma track_sc : track (scaling t F) x=(κ t 12) • track F (η t x):= by
   unfold track Rose.b3; simp_rw [scales]
   simp only [ show (W).card=3 from rfl,Finset.card_singleton]; simp (disch:=decide) only [ Finset.card_insert_of_notMem, Finset.card_singleton ]; norm_num1; -- implies RHS.Cost powers
   let H'(s:d):= spectrum F (η t x) s; let v:= κ t 4
   rw [ show κ t 8=v*v from (by unfold Extent.token v; ring), show κ t 12=v*v*v from (by unfold v Extent.token; ring) ]; simp only [two_smul, smul_add,smul_sub,mul_smul_comm,smul_mul_assoc ]; -- run module
   module -- coefficients commute
lemma scales_opp (F:Way G 4): Ξ n (track ( scaling t F ) x)= κ t 12 * Ξ n (track F (η t x)):= by rw [track_sc,map_smul]; rfl
end scale
end
end YM.SignedWilsonExpansion.Contrast
