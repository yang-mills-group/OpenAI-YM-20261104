import YM.FormalOPE.RG10.MarkovChain.Seating
/-!
 # Compressed tape of ordered elementary transfer in a chosen finite Cloth.
 Courses per transition may supply extra operator marks in Both adjacent variable windows;
 no requirement that they all come priced, dollar signs or disjoint subsets. This describes
 the ordinary coefficient algorithm. Support restrictions for physical OPE still not here. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (S:=S) (H:=H) (t:=t) (hf:=hf) (C:=C) (P:=P)
namespace Router
local notation "Ω"=> Field (Cloth.choose T0)
local notation "V"=> Field C.choose
local notation "F"=> Cross (G:=G) S P
local notation "N"=> Head C.choose
local notation "μ" => tangent G (Index S P)
local notation "ξ" => descendMap (S:=S) (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C)

-- have the prototype stored in Pair rather than justified d
 def incoming : Ω →ₗ[ℝ] F × N := ((LinearMap.id (M:=F) (R:=ℝ)).prodMap (send C.choose)) ∘ₗ (d).symm.toLinearMap
local notation "δ"=> incoming (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C)
lemma inflow (x y): δ (d (x,y))= (x,send C.choose y):= by simp [incoming]
lemma supportPair (u:Ticket (F × N)): Adjacent (boost δ u):= by intro x y z h; dsimp only; simp_rw [caught,inflow,h]
lemma liftOff (u:Ticket (F × N)): (boost ξ) ((boost δ) u) = u:= by apply into; rintro ⟨x,y⟩; rw [caught,caught,descend,inflow,send_place]
lemma at_once (Λ: Law Ω)(A:Ticket Ω)(Y:Ticket V)(W:Ticket Ω): delivered Λ d μ (A*Ancestor Y) W= delivered Λ d μ A W * Y:= by unfold delivered; rw [←mul_assoc, pullOut]; ring

abbrev Panel {n:Side}{L:Fabric G n}(T:Cloth L):= Ticket (Head T.choose)
 def Sack {n:Side}{L:Fabric G n}(T:Cloth L): Type := match T with
 | .floor _ _ _=> Panel T -- investigate motive
 | .inLayer (S:=S) P C=> Ticket (Cross (G:=G) S P × Head C.choose) × Sack C
-- maybe rec.zero
 def blank {n:Side}{L:Fabric G n}(T:Cloth L): Sack T:= match T with
 | .floor k h Q=> (1:Panel (Cloth.floor k h Q))
 | .inLayer _ C=>Prod.mk (1:Ticket (_×Head C.choose)) (blank C)
 def gauged {n:Side}{L:Fabric G n}(T:Cloth L)(J:Sack T): Ticket (Field T.choose):= match T with
 | .floor n h Q=> transmit (Cloth.floor n h Q) J -- Binder type reducible
 | .inLayer (S:=S) (b:=H) (t:=t) (h:=h) P C=> (boost (incoming (H:=H) (t:=t) (hf:=h) (P:=P) (C:=C)) (Prod.fst (β:= Sack C) J)) * Ancestor (gauged C (Prod.snd J))
-- rewrite hints to avoid semireducibility in simp
lemma nominal {n:Side}{L:Fabric G n}(T:Cloth L): gauged T (blank T)=1:= by
 cases T with
 | floor k h T=> show transmit (Cloth.floor n h T) 1=1; unfold transmit; rw [_root_.map_one]
 | @inLayer c f S H t h L P C=>
    let D:= incoming (H:=H) (t:=t) (hf:=h) (P:=P) (C:=C)
    change boost D 1 * Ancestor (gauged C (blank C))=1; unfold Ancestor; rw [nominal C,_root_.map_one,_root_.map_one,mul_one]
termination_by structural T

-- operate schedule already prepared. Don't need to integrate vacant slices.
 def migrate (Λ:Law Ω)(W:Ticket Ω) : Ticket V:= transmit C (nearest Λ μ (boost ξ (handle W))) * boost (coarse d) W
 def transport (Λ:Law Ω)(W:Ticket Ω)(A:Panel T0)(u:Ticket (F×N)):Panel C:= delivery Λ μ (boost ξ (transmit T0 A) * u) (boost ξ (handle W))
 def journey {n:Side}{L:Fabric G n}(T:Cloth L)(Λ:Law (Field T.choose))(J:Sack T)(A:Panel T)(W:Ticket (Field T.choose)): PowerSeries ℝ := match T with
 | .floor n h Q=> enjoy Λ (tangent G (Cloth.floor n h Q).choose.Bulk) (transmit (Cloth.floor n h Q) A * gauged _ J) W
 | .inLayer (S:=S) (b:=H) (t:=t) (h:=h) P C=> journey C (rest Λ (Pathway (H:=H) (t:=t) (hf:=h) (P:=P) (C:=C))) (Prod.snd J) (transport Λ W A (Prod.fst J)) (migrate Λ W)
lemma aligned (Λ:Law Ω) (J:Sack T0)(A:Panel T0)(W:Ticket Ω)(ht:Actual T0 Λ)(h:Vault T0 W)(he:incline W):
 transaction T0 Λ (transmit T0 A * gauged T0 J) W= transaction C (rest Λ d) (transmit C (transport Λ W A (Prod.fst J))* gauged C (Prod.snd J)) (reclose Λ d μ W):= by
 let u:Ticket (F × N):= Prod.fst J
 let v:Sack C:= Prod.snd J
 let X:= transmit T0 A; let B:= X * boost δ u
 rw [transaction]
 change transaction C (rest Λ d) (delivered Λ d μ (X * _) W) _= _; congr 1
 · change delivered Λ d μ (X * (boost δ u * Ancestor (gauged C v))) W= transmit C (transport Λ W A u) * gauged C v
   rw [←mul_assoc,at_once, authentic Λ μ ht (receive (presently (written _ _)) (supportPair u)) h he, _root_.map_mul (boost ξ), liftOff]; rfl

lemma completes {n:Side}{L:Fabric G n}(T:Cloth L)(Λ:Law (Field T.choose))(J:Sack T)(A:Panel T) {W:Ticket (Field T.choose)}(ht:Actual T Λ)(h:Vault T W)(he: incline W):
 journey T Λ J A W= transaction T Λ (transmit T A * gauged T J) W:= by
 cases T with
 | floor=> rfl
 | @inLayer c f S H t hf L P C=>
    rw [journey, aligned Λ J A W ht h he]; let D:= Pathway (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C)
    let w:= tangent G (Index S P)
    rw [show migrate Λ W = reclose Λ D w W from (onward Λ w ht h he).symm]
    exact completes C _ _ _ (forever Λ ht) (advance Λ w ht h he) (born_transfer Λ D w he)
termination_by structural T
end Router
end YM.FormalOPE.RG10.MarkovChain
