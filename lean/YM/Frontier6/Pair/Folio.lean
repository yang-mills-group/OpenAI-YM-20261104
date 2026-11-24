import YM.Frontier6.Pair.FixedWord
import YM.Frontier6.Pair.GridCapture

/-! The fused mark and exterior marks use the same grid, but different cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Function Filter Set Lattice Wilson RG Source MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Extraction Cells Around OS Word
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius

variable {G:Gauge}{C:Family G}{F:Extraction.Order} {f:Filter (ℕ×ℕ)}
variable {j k m b l n D d t : ℕ} (B:C.label d) (U:C.label t) (z:C.label D)
set_option quotPrecheck false

lemma at_origin {ℓ:ℕ}{X:ℕ×ℕ→ C.label D} (hf:f ≤ F.fuse) (hx:Tendsto X f (𝓝 (0:C.label D))) (h:Extraction.Wcmain C)
   (hℓ:C.ref D ≤ ℓ) (ε:ℝ) (he:0 < ε) : ∀ᶠ i:ℕ×ℕ in f, ∃ hN:ℓ ≤ i.1,
     let T:=center C.S i.2 hN 0
     Interior (T.chamber 0) (C.O i.1 i.2 (X i) 0)∧ T.rootTest (C.beta i.1 i.2) (C.O i.1 i.2 (X i) 0)≤ ε:=by
   obtain ⟨A,hA,hY⟩:= h D 1 1 one_pos one_pos
   let Z:= A*C.S.a ℓ^ (-(D:ℝ)-(1:ℝ)); have hZ:0 ≤ Z:=mul_nonneg hA (Real.rpow_nonneg (C.S.a_pos _).le _)
   let r:= ε/(1+Z); have hr:0 < r:=by unfold r; positivity
   let y i:= (r:ℂ)⁻¹ • X i; have hy : Tendsto y f (𝓝 0):=by simpa only [smul_zero] using! hx.const_smul (r:ℂ)⁻¹
   filter_upwards [(hy.norm.eventually (ge_mem_nhds (by simp : ‖(0:C.label D)‖ < 1))), (Push.RelayDifference.cutoff_grows F|>.mono_left hf).eventually (hY ℓ hℓ)] with i hi hU
   obtain ⟨hN,hr',hQ⟩:= hU i.2 (y i) hi
   have hE : C.O i.1 i.2 (X i) 0 = (r:ℂ) • C.O i.1 i.2 (y i) 0:= by
       rw [← (C.linearO i.1 i.2 D 0).map_smul,show (r:ℂ) • y i=X i from smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hr.ne') _]
   refine ⟨hN,?_⟩; intro T -- goal let?
   rw [hE]; refine ⟨(hQ 0).1.scale _,?_⟩
   rw [Next.Extract.root_smul,Complex.norm_real,Real.norm_of_nonneg hr.le];
   apply (mul_le_mul_of_nonneg_left (show T.rootTest _ _ ≤ Z from (hQ 0).2) hr.le).trans
   exact (mul_le_mul_of_nonneg_left (show Z ≤ 1+Z by linarith only) hr.le).trans_eq (div_mul_cancel₀ ε (by linarith only [hZ]))

structure RealPair (B:C.label d)(U:C.label t)(z:C.label D)(b j:ℕ)(x:Lattice.Cover)(ε:ℝ) (f:Filter (ℕ×ℕ)): Prop where
    fits:∀ᶠ i:ℕ×ℕ in f, ∃ h:b ≤ i.1,
       let T:=center C.S i.2 h 0; let u:= pairFragment C j d t D x B U i.1 i.2 z
       Interior (T.chamber 0) u ∧ T.rootTest (C.beta i.1 i.2) u ≤ ε

lemma realize_limit (hF:f ≤ F.fuse) (X:Rowe C D) (ht:Tendsto X f (𝓝 z)) (x:Lattice.Cover) (ε ε':ℝ)
   (he:ε<ε')(hC:C.Makes)(h:Extraction.Wcmain C)(hD:C.ref D ≤ b) (hp:∀ᶠ i:ℕ×ℕ in f, ∃ h:b ≤ i.1,
       let T:=center C.S i.2 h 0; let u:= pairFragment C j d t D x B U i.1 i.2 (X i)
       Interior (T.chamber 0) u ∧ T.rootTest (C.beta i.1 i.2) u ≤ ε) : RealPair B U z b j x ε' f:=by
    have hx:Tendsto (fun i=>X i-z) f (𝓝 0):=by simpa using! ht.sub_const z
    constructor; filter_upwards [hp,at_origin hF hx h hD (ε'-ε) (sub_pos.mpr he)] with i hi hu
    obtain ⟨N,p⟩:=i; obtain ⟨hN,hZ,hq⟩:=hi; obtain ⟨hr,hU,hV⟩:=hu
    let T:= center C.S p hN 0
    let f(z:C.label D):= pairFragment C j d t D x B U N p z
    let u:= C.O N p (X (N,p)-z) 0
    have he : f z=f (X (N,p))+u:=by
       unfold f u; rw [show C.O N p (X _-z) 0=C.O N p (X (N,p)) 0-C.O N p z 0 from (IsLinearMap.mk' _ (C.linearO N p D 0)).map_sub ..]; unfold pairFragment; abel
    refine ⟨hN,?_⟩; change Interior (T.chamber 0) (f z) ∧ T.rootTest _ (f z) ≤ _; rw [he]; refine ⟨hZ.plus hU,?_⟩
    exact ((seamless hC N p).semi T _ _ hZ hU).trans ((add_le_add hq hV).trans_eq (add_sub_cancel _ _)) -- check

variable (v:Fin n → C.book.Token)

def seatsPair (v:Fin n → C.book.Token) (p:C.book.Token) := Fin.cons (α:=fun _ : Fin (n+1)=> C.book.Token) p v

def wordPrice (x:E4) (y:Points n)(S:Table C.book) := S.read (Points.cons x (Points.cons 0 y)) (seatsPair (seatsPair v ⟨d,B⟩) ⟨t,U⟩)- S.read (Points.cons 0 y) (seatsPair v ⟨D,z⟩)

-- one board story on true kernel. common mesh l≥j.
variable (x:Lattice.Cover)(u:Fin n → Lattice.Cover)
set_option quotPrecheck false
local notation "y"=> Extraction.Order.grid C l u
variable (hU:j ≤ l) (hx: Points.cons (C.S.gridPoint j x) (Points.cons 0 (Extraction.Order.grid C l u)) ∈ generic (n+2))

def secondPoint (u:Fin n → Lattice.Cover)(x:Lattice.Cover) : Fin (n+2) → Lattice.Cover := Fin.cons x (Fin.cons 0 u)
lemma high_grid : Extraction.Order.grid C l (Fin.cons 0 u)= Points.cons 0 (y) := by
    ext1 i; refine Fin.cases ?_ (fun j=>?_) i
    · simp [Extraction.Order.grid,Points.cons,Schedule.gridPoint]
      rfl
    rfl
lemma full_grid (hU:j ≤ l) : Extraction.Order.grid C l (secondPoint u (pushSite C.S hU x))= Points.cons (C.S.gridPoint j x) (Points.cons 0 (y)):= by rw [← high_grid]; ext1 i; refine Fin.cases ?_ (fun k=>?_) i; exact finer ..; rfl
include hx
lemma second_generic : Points.cons (0:E4) (y)∈generic (n+1):= by
   intro i k m h; exact Fin.succ_inj.mp (hx i (show (Points.cons (C.S.gridPoint j x) (Points.cons 0 (y)) k.succ i)= (Points.cons (C.S.gridPoint j x) (Points.cons 0 (y)) m.succ i) from h))

private def two {M:Fin 2→Type} (x:M 0)(y':M 1) : ∀ i:Fin 2, M i := Fin.cases x (Fin.cases y' (fun i=> Fin.elim0 i)) -- defeq?

include hU
private def doubleStory (F:Extraction.Order) : Episode C F l :=
    let n':Fin 2→ℕ:=![n+2,n+1]; let Y:Π i:Fin 2,Fin (n' i)→ Lattice.Cover:= two (secondPoint u (pushSite C.S hU x)) (Fin.cons 0 u)
    let Z:Π i:Fin 2,Fin (n' i)→ C.book.Token:= two (seatsPair (seatsPair v ⟨d,B⟩) ⟨t,U⟩) (seatsPair v (⟨D,z⟩:C.book.Token))
    stillStory F 2 l ![1,-1] n' Y Z fun i=>by
       fin_cases i
       · change Extraction.Order.grid C l (secondPoint u _)∈_
         exact full_grid (C:=C) x u hU|>.symm ▸ hx
       change Extraction.Order.grid C l (Fin.cons 0 u) ∈ generic (n+1)
       exact high_grid (C:=C) u|>.symm ▸ second_generic x u hx -- need defeq two eval

local notation "E"=> doubleStory B U z v x u hU hx F

lemma double_price (F:Extraction.Order)(S:Table C.book): fieldWord (doubleStory B U z v x u hU hx F) S= wordPrice B U z v (C.S.gridPoint j x) y S:=by
    let T:= S; unfold fieldWord; -- change two terms manually
    let e:= doubleStory B U z v x u hU hx F
    change (∑ i: Fin 2,e.factor i * S.expect (e.word i)) = _
    rw [Fin.sum_univ_two]
    change 1*S.expect (realize _ (Extraction.Order.grid C l (secondPoint u (pushSite C.S hU x)))) + (-1)*S.expect (realize _ (Extraction.Order.grid C l (Fin.cons 0 u)))=_
    rw [S.readAt,S.readAt]
    change 1*S.read (Extraction.Order.grid C l (secondPoint u (pushSite C.S hU x))) (seatsPair (seatsPair v ⟨d,B⟩) ⟨t,U⟩)+ (-1)*S.read (Extraction.Order.grid C l (Fin.cons 0 u)) (seatsPair v ⟨D,z⟩)=_
    rw [full_grid,high_grid]; unfold wordPrice; ring

lemma double_cuts {N p:ℕ} (hN:l ≤ N)(F:Extraction.Order) (Y:Config G (C.side N p)) :
    (doubleStory B U z v x u hU hx F).cuts N p 0 Y= pairFragment C j d t D x B U N p z Y*∏ i:Fin n,C.O N p (v i).2 (location C.S l N p (u i)) Y:=by
    unfold Episode.cuts
    let e:= doubleStory B U z v x u hU hx F
    change (∑ i: Fin 2,e.factor i * ∏ j: Fin (e.image i), C.O N p (e.current i j N p) (Cells.location C.S l N p (e.seats i j+0)) Y)= _
    rw [Fin.sum_univ_two]; simp only [add_zero]; change 1* (∏ i:Fin (n+2),C.O N p ((seatsPair (seatsPair v ⟨d,B⟩) ⟨t,U⟩) i).2 (Cells.location C.S l N p (secondPoint u (pushSite C.S hU x) i)) Y)+ (-1)* (∏ i:Fin (n+1),C.O N p ((seatsPair v ⟨D,z⟩) i).2 (location C.S l N p (Fin.cons (α:=fun _=>Lattice.Cover) 0 u i)) Y)=_
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.prod_univ_succ]
    let P:=∏ i:Fin n,C.O N p (v i).2 (location C.S l N p (u i)) Y
    change 1* (C.O N p U (location C.S l N p (pushSite C.S hU x)) Y*(C.O N p B (location C.S l N p 0) Y * P)) +
       (-1)* (C.O N p z (location C.S l N p 0) Y * P)=_
    rw [location_origin,location_down _ hU hN]; change _ =(C.O N p B 0 Y*C.O N p U (location C.S j N p x) Y-_)*P; ring -- hN
variable {S:Table C.book} (K:Spec.Final C F S)
open Org in
lemma fixed_ports (h:Grill C F) (c:Fin n → Lattice.Cover)
    (hc:Injective (Fin.cons (α:=fun _ : Fin (n+1)=> Lattice.Cover) 0 c)) (s:StateIndex K) (hf:f ≤ F.fuse)[f.NeBot]
    (hb:b ≤ l)(r:Fin n→ℝ)(hr:∀ i,0 ≤ r i)(ε:ℝ)(hε:0 ≤ ε)(H:RealPair B U z b j x ε f)
    (hp:∀ j:Fin n,∀ᶠ i:ℕ×ℕ in f, ∃ (h:b ≤ i.1)(g:Config G (C.side i.1 i.2)→ℂ),
          let T:= center C.S i.2 h 0
          Interior (T.chamber 0) g ∧ T.rootTest (C.beta i.1 i.2) g ≤ r j ∧
          C.O i.1 i.2 (v j).2 (Cells.location C.S l i.1 i.2 (u j))=T.copy (wrap T.period (c j)) g):
        ‖wordPrice B U z v (C.S.gridPoint j x) y (state K s)‖ ≤ ε*∏ i:Fin n,r i:=by
   let c':Fin (n+1) → Lattice.Cover := Fin.cons 0 c
   let r':Fin (n+1)→ℝ:=Fin.cons ε r
   have hr': (∏ i,r' i)=ε*∏ i,r i:=by unfold r'; rw [Fin.prod_univ_succ]; simp
   rw [← double_price B U z v x u hU hx F,← hr']; apply lectern K E c' hc s h hb hf r' (Fin.cases (motive:=fun i=> 0≤ r' i) hε (fun i=>hr i));
   filter_upwards [H.fits,eventually_all.mpr hp,Eventually.filter_mono hf (large_mesh F l)] with i hZ hu hi
   obtain ⟨N,p⟩:=i; obtain ⟨hN,h',h''⟩:=hZ; let Z:=pairFragment C j d t D x B U N p z
   choose h₀ Q h₁ using hu
   let f:Fin (n+1)→ Config G (C.side N p)→ℂ:= Fin.cons Z Q
   let T:=center C.S p hN 0
   refine ⟨hN,f, fun i=>?_,?_⟩
   · change Interior (T.chamber 0) (f i) ∧ T.rootTest _ (f i) ≤ _
     refine Fin.cases (motive:=fun i=> Interior (T.chamber 0) (f i) ∧ T.rootTest (C.beta N p) (f i) ≤ r' i) ⟨h',h''⟩ (fun i=> ?_) i
     exact ⟨(h₁ i).1,(h₁ i).2.1⟩
   funext X; rw [double_cuts B U z v x u hU hx hi F]
   rw [Fin.prod_univ_succ]; change Z _ * _= T.copy (wrap T.period 0) Z _ * _; rw [map_zero,Tiling.copy_zero]; congr 1
   exact Finset.prod_congr rfl (fun i _=> congr_fun ((h₁ i).2.2) X)
end YM.Frontier6.Platform
