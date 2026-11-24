import YM.MSbar.Jade.Signals
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Jade
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
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
noncomputable def chairP (F:Forest S.ratio)(v:S.Choices)(R:Rep G f)(x:Positions (Primary c G)):= linCash F x -- ok
local notation "f1"=>linCash F (t • Z)
local notation "I!"=>hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
variable (h: S.patch.Branches S.kernel G)(hp:Premier (Rolling.main f R.clip R.path))(hz:Critical F R.clip R.path ρ) (hh:ClassicalMatch F R.clip l R.path e ρ) (hd:(mold R F v).PosDef)(ht:0<t)
noncomputable abbrev sampleY (U':Config G f)(x:Positions (Primary c G)):= him J F Y (represent (tint G _ x)) (vest (priced F v R.clip R.path) x) (mold R F v) X (chairP F v R x) U'
-- section forces binder order.F R v J X Y. ok
local notation "c!"=> sampleY F R v J X Y U' (t • Z)
local notation "g"=> center F ρ
section
variable {ι σ:Type}[Fintype ι][DecidableEq ι][Fintype σ][DecidableEq σ]
    {T':Matrix σ σ ℝ}
lemma shellK (u:ι→σ)(b: View σ)(x:View ι)(he:T'.PosDef)(hu:Injective u):let P:=imbed u*ᵥ x; let v:=vanish u T'*ᵥb
   dotProduct (v+P) (T'*ᵥ(v+P))/2 = dotProduct v (T'*ᵥv)/2+dotProduct x (pinch u T'*ᵥ x)/2:=by
     intro p v; let A:=imbed u; let D:=vanish u T'
     have ht:T'.transpose=T':=by simpa [Matrix.IsHermitian] using he.1
     have hx: D.transpose * T'= T'*D:=by
          have hv: (extendM u (pinch u T')⁻¹).transpose=extendM u (pinch u T')⁻¹ := by rw [extendM,transpose_mul,transpose_mul,transpose_transpose]; have hh : Matrix.PosDef (show Matrix ι ι ℝ from (pinch u T')⁻¹):= (he.submatrix hu).inv; rw [show ((pinch u T')⁻¹).transpose= _ from (by simpa [Matrix.IsHermitian] using hh.1 : ((pinch u T')⁻¹).transpose=(pinch u T')⁻¹), Matrix.mul_assoc]; -- redo
          unfold D Kelvin.vanish; rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_mul,hv,ht, Matrix.sub_mul, Matrix.mul_sub, one_mul, mul_one, Matrix.mul_assoc]
     have hc: dotProduct v (T'*ᵥ p)=0:=by
         change dotProduct (D *ᵥ b) (T'*ᵥp)=0; rw [dotProduct_comm, dotProduct_mulVec,← Matrix.mulVec_transpose,mulVec_mulVec,hx, dotProduct_comm]; unfold p; rw [mulVec_mulVec,Matrix.mul_assoc, show D * imbed u=0 from planted u hu he]; simp
     have hp : dotProduct p (T' *ᵥ v)=0:=by rw [dotProduct_mulVec,← Matrix.mulVec_transpose,ht,dotProduct_comm]; exact hc
     have hy : dotProduct x ((pinch u T') *ᵥ x)=dotProduct p (T'*ᵥ p):=by rw [dotProduct_comm p, show p=A*ᵥ x from rfl, dotProduct_mulVec (T' *ᵥ(A*ᵥx)) _,← Matrix.mulVec_transpose, dotProduct_comm _ x, clipped,Matrix.mul_assoc,← mulVec_mulVec,←mulVec_mulVec]
     rw [Matrix.mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add,hc,hp,hy];ring
end
include h hp hz hh hd ht
lemma loves:sampleY F R v J X Y U' (t • Z)= t • center F ρ Z + vanish Λ H*ᵥ outY J F Y (postcard G c t Z) ν X (linCash F (t • Z)) U' :=by
    rw [← map_smul,lovely F v R.path R.clip ρ h hp hz _ hd]; rfl
noncomputable def berth (U':Config G f)(x:Positions (Primary c G))(t:ℝ) : SpaceP F X G → Positions (Key F G):=fun y=> t⁻¹ • sampleY F R v J X Y U' (t•x)+ (Kelvin.imbed (includeX (G:=G) F X))*ᵥ y -- binder order
local notation "U"=>berth F R v J X Y U' Z t
local notation "S₀"=> straight F G
lemma appeal (x y:SpaceP F X G):
      let φ:=potter (pushChart F G v) 2; let h(u: X₀):= height f R.clip R.path (stamp F G (berth F R v J X Y U' Z t u))+ MvPolynomial.eval (meetVar Z (berth F R v J X Y U' Z t u)) φ
      h x-h y= dotProduct x (((pinch (includeX (G:=G) F X) (mold R F v)))*ᵥ x)/2-dotProduct y (((pinch (includeX (G:=G) F X) (mold R F v)))*ᵥ y)/2:=by
      intro φ k; let p:= Λ; let L':= outY J F Y (postcard G c t Z) ν X f1 U'; let b:=t⁻¹ • L'; let j:=vanish p H*ᵥ b; let I(u:X₀):= imbed p*ᵥ u
      have he(x:X₀):U x=g Z+(j+I x):=by unfold berth; rw [loves F R v J X Y U' t Z e l ρ h hp hz hh hd ht, smul_add,inv_smul_smul₀ ht.ne', ← Matrix.mulVec_smul,add_assoc]; -- syntax
      have hx(x:X₀): k x=height c l e Z + dotProduct j (H*ᵥj)/2 + dotProduct x ((pinch Λ H)*ᵥ x)/2:=by unfold k φ; rw [he,pots, steady F v R.path e R.clip l ρ h hp hz hh]; change _+dotProduct _ _/2= _; rw [show dotProduct _ _ /2= dotProduct j (H*ᵥj)/2+dotProduct x _/2 from shellK p b x hd (secureY F X G)]; ring
      rw [hx,hx];ring
end YM.MSbar.Jade
