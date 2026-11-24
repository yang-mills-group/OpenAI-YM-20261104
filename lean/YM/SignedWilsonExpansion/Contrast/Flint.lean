import YM.SignedWilsonExpansion.Contrast.Emerald
/- # ground cancellation for arbitrary through FOUR U→V compensated columns, not just near identity -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SignedWilsonExpansion.Carbon.Flint
open FVA2 Register FVA2.Arrival Scale Scale.Jury MS MS.Menus MS.High MS.Local.Physical MS.Native MS.Land MS.Fleet
open MeasureTheory Function Filter Set XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Asymptotics PowerSeries Maxwell Maxwell.Free
open WickFace ProbeB Contrast Belle Belle.Path Belle.Buffet WilsonCoeffUV.Mer.Xa MarqueQ Crops Scale.Level Scale.Equator Scale.Facets
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} (N: WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q)
local notation "W"=> ( Measure.start N.scheme N.criterion 4 )
local notation "Z"=> N.scheme
local notation "ψ"=> N.criterion
local notation "Q'"=> H.details.toServed.toPosted.toQuoted.toContract.toMission.born
variable (i:Fin 3)(x: Scale.Stage 3)
local notation "θ"=> Sec G 4
local notation "Φ"=> Extent.token
local notation "Y¹"=> Tags G 4 3
local notation "Ξ"=> leaf G 4
abbrev typist (b:Way G 4)(m:Rose.Badge) (v: Tags G 4 3)(y:Points 3): PowerSeries ℂ:= mk fun i=> Jury.fxt b y i ( Rose.missing v m )
abbrev compiled (b:Way G 4)(v: Tags G 4 3)(x:Points 3):= Rose.b3 fun i=>typist b i v x
include H
omit H in
abbrev pole (i:Fin 3) (x:Scale.Stage 3): FieldEnd G 4:= 1-LinearMap.smulRight ( coin (G:=G) x i ) ( leaf G 4 )
omit H in
lemma pole_at (v:Sec G 4): pole i x v=v - coin x i v • leaf G 4:=rfl
private lemma centered (u:θ)(x' : Scale.Stage 3)(t:ℝ): Dial 4 t ( pole i x u )= Φ t 4 • pole i x' u:=by
    refine WickFace.at_low h ( ( Dial 4 t ).comp ( pole i x ) ) (Φ t 4 • pole i x') ?_ ?_ u
    · have he(y:Scale.Stage 3): pole i y (Ξ)= (0:Sec G 4):= by rw [pole_at,show coin y i (Ξ)=1 from coinS y i,one_smul,sub_self ]
      rw [LinearMap.comp_apply, he, map_zero, LinearMap.smul_apply,he,smul_zero] -- ; scope hazard
    intro j k; have he(y: Scale.Stage 3) : pole i y (glow G j k) = glow G j k:=by rw[ pole_at, show coin y i (glow G j k)=0 from single_off (G:=G) y i j k,zero_smul,sub_zero ]
    rw [LinearMap.comp_apply,he, WickFace.money,LinearMap.smul_apply,he]
-- coefficient-zero centering identity. proof for any trilinear incl true unit.
omit H in
lemma algebra {K:Type}[_root_.Field K]{V:Type}[AddCommGroup V][Module K V] (F:MultilinearMap K (fun _ : Fin 3 => V) K) (u:V)(v: Fin 3→ V) (H: F ![u,u,u] =1):
     let I(s: Finset ( Fin 3 )):= F ( fun i=> if i∈s then v i else u ); I Finset.univ - ( I {0,1} * I {2} + I {0,2} * I {1} + I {1,2} * I {0} ) + 2*( I {0} * I {1} * I {2} ) = F fun i=> v i - I {i} • u := by
    let I(s: Finset ( Fin 3 )):= F ( fun i=> if i∈s then v i else u ); let f(a b c:V):=F ![a,b,c]; let x:= v 0; let y:=v 1; let z:=v 2
    have wt0 (a b c: V) (k:K): f ( a - k • u ) b c=f a b c-k * f u b c:= by
        let v:Fin 3→V:= ![a,b,c]; have ht(w:V): f w b c= F.toLinearMap v 0 w:=by apply congr_arg F; funext i; fin_cases i<;> rfl
        rw [ht, map_sub,map_smul, ht,ht]; rfl
    have wt1 (a b c:V) (k:K): f a ( b - k • u ) c=f a b c-k*f a u c:=by
        let v:Fin 3→V:=![a,b,c]; have ht(w:V): f a w c= F.toLinearMap v 1 w:=by apply congr_arg F; funext i; fin_cases i<;> rfl
        rw [ht,map_sub,map_smul,ht,ht]; rfl
    have wt2 (a b c:V) (k:K): f a b ( c - k • u )=f a b c-k*f a b u:=by
        let v:Fin 3→V:=![a,b,c]; have ht(w:V): f a b w=F.toLinearMap v 2 w:=by apply congr_arg F; funext i; fin_cases i<;> rfl
        rw [ht,map_sub,map_smul,ht,ht]; rfl
    change I _-(I _*I _+I _*I _+ I _*I _) + 2*(I _*I _ * I _) = _
    have he (w: Fin 3→V): F w = f (w 0) (w 1) (w 2):=by apply congr_arg F; funext i; fin_cases i<;> rfl
    rw [ he,wt0 ]; simp_rw [wt1,wt2]
    dsimp only [ I ]; simp_rw [ he ( fun i=> ite _ _ u ) ]; simp (disch:=decide) only [ if_pos,if_neg ] -- unfold needs decidableEq u? adjust
    rw [show f u u u=1 from H]; ring
variable (ν:ℝ)
include ν
lemma hugs (v: Tags G 4 3) : coeff 0 ( compiled W v x.val ) = iris x ( fun i=> pole i x (v i) ) :=by
    have HE:= ( AxialBill.snapshot Y Z ψ S h (Q').Taylor (Q').still (Q').base ν x ).1
    have he(i:Rose.Badge): coeff 0 ( typist W i v x.val )=iris x ( Rose.missing v i ):= by unfold typist; rw [coeff_mk,Jury.exactC, HE]
    let u:= leaf G 4; let T:= iris x (G:=G) (d:=4); let I(s:Rose.Badge):=iris x ( Rose.missing v s ); have hS(i:Fin 3): I {i}=coin x i (v i):=by
        have hx: Rose.missing v {i}=update (fun _=>u) i (v i):=by ext1 a; by_cases ha:a=i <;> simp [ ha,Rose.missing,u ]
        unfold I; rw [ hx ]; exact iris_one ..
    unfold compiled Rose.b3; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp only [two_smul,map_add,map_mul,map_sub,←PowerSeries.coeff_zero_eq_constantCoeff_apply,he]; change I _ -( I _ * I _ + I _ * I _ + I _ * I _ ) + ( I _ * I _ * I _ + I _ * I _ * I _ ) = _
    rw [ ← two_mul ]; refine Eq.trans (algebra T u v ( ?_ )) (?_)
    · have ht: ![u,u,u]= ( fun _=>u:Fin 3→ θ ):=by funext i; fin_cases i <;> rfl
      rw[ ht ]; exact (show iris x _=1 from Maxwell.Wick.constants (G:=G) x.val ) -- formatting
    apply congr_arg T; funext a; rw [pole_at]; rw [← hS a]; rfl
lemma tide (t:ℝ)(v: Tags G 4 3): Φ t 12 * coeff 0 ( compiled W v ( posing t x ).val ) = coeff 0 ( compiled W v x.val ):=by
    rw [hugs N H _ ν,hugs N H _ ν]; let x' := posing t x; have hu(i:Fin 3):= centered N H i x (v i) x' t; let y(i):= pole i x (v i); let y'(i):= pole i x' (v i); have hp:= iris_s Y Z S h (Q').Taylor x y t
    rw[ show Dial 4 t ∘ y=fun i=> Φ t 4 • y' i from funext hu, MultilinearMap.map_smul_univ ] at hp; rw [show Φ t 12=∏ i:Fin 3,Φ t 4 from by rw[ Fin.prod_univ_three ]; unfold Extent.token; ring]; exact hp
lemma snow (v:Tags G 4 3): coeff 1 ( compiled W v x.val )=0:=by
    have HP:= ( AxialBill.snapshot Y Z ψ S h (Q').Taylor (Q').still (Q').base ν x ).2.2.1; have HE(m:Rose.Badge): coeff 1 ( typist W m v x.val )=0:=by unfold typist; rw[ coeff_mk,Jury.exactC, HP ]; rfl
    unfold compiled Rose.b3; simp only[map_add,map_sub,map_smul, coeff_one_mul, HE,mul_zero,zero_mul, add_zero, smul_zero,sub_zero]
end YM.SignedWilsonExpansion.Carbon.Flint
