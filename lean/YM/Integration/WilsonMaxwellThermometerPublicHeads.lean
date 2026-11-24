import YM.Integration.WilsonMaxwellThermometerPublicEvenSlope
import YM.Integration.WilsonMaxwellThermometerChargedHeads
/-! The entire finite position thermometer, evaluated on the enrolled field
basis. Its first signed response sees precisely the three maximal degree
blocks. Every unit and lower fitted field retains its voted face. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicHeads
open Function Finset Set Lattice Labels Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 XSpace.Graph3 XSpace.Photo XSpace.Rose
open WilsonMaxwellThermometerChargedHeads WilsonMaxwellThermometerPublicGalop
open WilsonMaxwellThermometerPublicEvenSlope WilsonMaxwellThermometerFirstDetector
open scoped Classical BigOperators
variable {G:Gauge}(W:Initialize G){V:Normalize.Store G}(x:Sample 3)

private theorem unit (p:Tags G 6 3)(j:Fin 3)(z:ℂ)(w:Sec G 6):
    node W (V:=V) x (update p j (w+z • leaf G 6))=node W (V:=V) x (update p j w):=by
  have paid:=WilsonMaxwellThermometerPublicUnit.original W (V:=V) x (update p j (leaf G 6)) j
    (Function.update_self ..)
  simp only [←enrolled,(sampled W (V:=V) x).map_update_add,(sampled W (V:=V) x).map_update_smul]
  change (sampled W (V:=V) x) (update p j w) + z • (sampled W (V:=V) x) (update p j (leaf G 6)) = _
  rw [enrolled W x (update p j (leaf G 6)),paid,smul_zero,add_zero]

theorem bottom (p:Sec G 6)(u v:Sec G 4)(t z:ℂ):
    node W (V:=V) x (entered p (u+t • leaf G 4) (v+z • leaf G 4))=
    node W (V:=V) x (entered p u v):=by
  have e1 (y:Sec G 4)(c:ℂ):update (entered p u y) 1 (up (by decide:4≤6) u+c • leaf G 6)=
      entered p (u+c • leaf G 4) y:=by
    funext i
    fin_cases i <;> rfl
  have e2 (c:ℂ):update (entered p u v) 2 (up (by decide:4≤6) v+c • leaf G 6)=
      entered p u (v+c • leaf G 4):=by
    funext i
    fin_cases i <;> rfl
  have hold (y:Sec G 4):update (entered p u y) 1 (up (by decide:4≤6) u)=entered p u y:=by
    funext i;fin_cases i <;>rfl
  have hold':update (entered p u v) 2 (up (by decide:4≤6) v)=entered p u v:=by
    funext i;fin_cases i <;>rfl
  rw [←e1,unit W x,hold,←e2,unit W x,hold']

theorem original (simple:G.Simple)(stage:V.Meets W x.F 6)
    (F:Labels.Frame G 6)(H:Labels.Frame G 4)(b:F.Coeff)(u v:H.Coeff):
    node W (V:=V) x (entered (sector F b) (sector H u) (sector H v))=
    node W (V:=V) x (entered (sector F (head F b)) (sector H (head H u)) (sector H (head H v))):=by
  rw [low H simple u,low H simple v,bottom W x]
  let p:=sector F (head F b)
  let e:=sector F b-p
  have same:p+e=sector F b:=add_sub_cancel _ _
  rw [←same]
  exact coefficient W simple x stage p e (even F simple b) _ _

end YM.Integration.WilsonMaxwellThermometerPublicHeads
end
