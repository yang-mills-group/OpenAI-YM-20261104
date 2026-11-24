import YM.FormalOPE.RG10.Compass.Margins
/-! Insert conversions in the same dictionary. No metric pole here. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Compass
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d n:ℕ} (s:Signed)
local notation "J" => Deck F d
local notation "T" => PertExtension.Physical.Profile
local notation "ℳ" => Mark J PertExtension.Physical.Profile.n
local notation "💠" => RG10.Position.deck F d
local notation "S" => RG10.Position.Grade.swing (F:=F) d s
local notation "ins" => PertExtension.Position.insert J PertExtension.Physical.Profile.n
local notation "oper" => operator (L:=Maxwell.standard F) (💠)

def rotate (v: ℳ) : ℳ := RG10.Profile.task (tilted s v.1.test) v.2
lemma oriented_top {A:Matrix J J ℝ} (hu:Oriented F d A) : A*S=S*A := by
 let f (p:Table.Field (freeTable F) d)(i:J):= (💠).repr p i
 ext i j; apply Complex.ofReal_injective; simp only [Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul, Grade.swing_deck]
 have he k : ride F s.ortho d ((💠) k)=∑ x, f (ride F s.ortho d ((💠) k)) x • ((💠) x):=((💠).sum_repr _).symm
 let T' : Module.End ℂ ((freeTable F).Field d) := oper A
 have ht i:T' ((💠) i)=∑ j, (A i j:ℂ) • ((💠) j):= operator_basis (L:=Maxwell.standard F) (💠) A i
 have hh: T' (ride F s.ortho d ((💠) i))= ride F s.ortho d (T' ((💠) i)):= DFunLike.congr_fun (hu.signed s) ((💠) i)
 nth_rw 1 [he] at hh
 simp_rw [ht,map_sum,map_smul,ht] at hh
 have hv:= congr_arg (fun p=> (💠).repr p j) hh; simp_rw [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply] at hv
 have he (q:J→ℂ) : (💠).repr (∑ j,q j • (💠) j) j=q j:= by rw [map_sum,Finsupp.finsetSum_apply]; simp [-deckAt,Finsupp.single_apply]
 simp_rw [show ∀ i, (💠).repr (∑ j,(A i j:ℂ) • (💠) j) j = ((A i j):ℂ) from fun i=> he _] at hv
 -- oriented direction
 simpa [f] using hv.symm

lemma posed_matrix (P:Plan F)(h:Official P.stock)(q m) : of (P.poses q m d) * (S).map C = (S).map C * of (P.poses q m d):= by
   let L (i:ℕ) : Matrix J J ℝ:= of fun x y=> coeff i (P.poses q m d x y)
   have he (i:ℕ) : L i*S=S*L i:= by
     obtain ⟨Z,hZ,_,hv⟩:= Plan.state h q m d i
     unfold L; rw [hv]; split
     · have hz : of (Physical.diag J+Z)=(1:Matrix J J ℝ)+ of Z:= by ext i j; by_cases h:i=j <;> simp [Physical.diag,h]
       rw [hz,add_mul,mul_add,one_mul,mul_one,oriented_top (A:=of Z) s hZ]
     exact oriented_top s hZ
   ext i j : 1; ext k : 1; simp only [Matrix.mul_apply, map_sum,Matrix.of_apply,Matrix.map_apply,coeff_C_mul,coeff_mul_C];
   exact congr_fun₂ (he k) i j

section
lemma Ribbon.turning (Φ: ℳ → fps) (B:Matrix J J fps) : ins (Φ ∘ rotate s) B=ins Φ B ∘ rotate s:= rfl
lemma Ribbon.cross_insert (Φ: ℳ → fps) (B A:Matrix J J fps) (h:B*A=A*B) : ins (ins (Φ ∘ rotate s) A) B = ins (ins Φ B) A ∘ rotate s := by
 rw [insert_twice,insert_twice]; change PertExtension.Position.insert J _ (Φ ∘ rotate s) (B*A)= _; rw [h]; exact Ribbon.turning ..

lemma Ribbon.promotes (Φ: ℳ → fps) (B:Matrix J J fps) (v: ℳ){Y: Drivers}{x: ℕ+→ℕ→ ℳ →fps} (u : ∀ z: ℳ,Y.Credit (fun q m=>x q m z) (Φ z)) : Y.Credit (fun q m=> ins (x q m) B v) (ins Φ B v):= by
 let b (g:Fin v.1.n→J):= ∏ i,B (v.2 i) (g i)
 exact Drivers.Credit.summons (x:=fun (g:Fin v.1.n→J) q k=>x q k ⟨v.1,g⟩ * b g) (A:=fun g=>Φ ⟨v.1,g⟩ * b g) univ (fun g _ => Drivers.Credit.cartesian (u ⟨v.1,g⟩) (Drivers.Credit.permanent _))
end
end YM.FormalOPE.RG10.Compass
