import YM.MS.Lifting.Letters
import YM.MS.Mach.Pol
import YM.MS.Mach.Spray
import YM.MS.Motif.Alpha
import YM.MS.Motif.Warp

set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Pilot Garment Color Book Convolve
open Motif Literal Halo Native Detect Lifting
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {k n:ℕ} {z:ℂ} {F H:Rack G n} {U:Mield G n}
local notation "Ψ"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local notation "Δ"=> forge ( Motif.dot (applyS z G n))
local notation "Ω"=> cwave n G
def Pole (G:Gauge)(n:ℕ)(i j: Axis)(z:ℂ) : List Axis→ Mield G n
 | []=> cur z (chair n i) (chair n j)
 | a::l=> convoke z (chair n a) (Pole G n i j z l)
def Pole_leaf (z:ℂ)(a:Plaq): Mield G n:= Pole G n a.i a.j z a.jets -- Ordered covariant derivatives of the curvature Fᵢⱼ at coupling z, with the list head acting outermost.
variable (i j:Axis)
namespace Pole
lemma ingot (l:List Axis): Apple (Pole G n i j z l) ∧ Mood false (Pole G n i j z l) := by
    induction l with
    | nil=> exact ⟨Apple.spicy _ _, Motif.curs ..⟩ -- h elaboration
    | cons a l ih=> exact ⟨Apple.heat _ ih.1, heatSA z _ _ ih.2 _⟩
lemma nice (l:List Axis)(a:G.ColorIndex): Symm Ψ (Pole G n i j z l a):= by
    induction l generalizing a with| nil=> exact Cur_sym _ _ _ _| cons k l ih=> let S:= chair n k; let P:= Pole G n i j z l; apply (m_sp (ih a) (δ S)).add; exact (vect_sym (H:=P) (F:=Motif.A n G S) a (fun i=> note_sym ( at_g S i ) (fun _:SectorP n=> (1:ℂ))) ih).smul z
lemma secret (l:List Axis) : Δ (Pole G n i j z l)= z • jaw G n (Pole G n i j z l) Ω:= by
    induction l with
    | nil=> exact horr ..
    | cons a l ih=>
        let P:= Pole G n i j z l; let D:=chair n a; have ht : jaw G n (convoke z D Ω) P = -jaw G n P (convoke z D Ω):= (by simpa only [cross_false',neg_one_smul] using (jaw_skew ( heatSA z _ _ ghMd D ).tune ( (ingot i j l).2.tune )))
        rw [Pole,S_D, ih,map_smul,civil_d z D (ingot i j l).2.tune,ht,smul_add]; simp [P,D] -- defeq D/P?
lemma guarded (l:List Axis)(a:G.ColorIndex): Safe (Pole G n i j z l a) z := Coven (ingot i j l).1 (nice i j l) (ingot i j l).2 (secret i j l) a
abbrev Sky (G:Gauge):= ∀ n:ℕ,Mield G n
def spinD (a:Axis)(G:Gauge) : Sky G→ₗ[ℂ] Sky G where
   toFun U n:= axisP (chair n a) (U n)
   map_smul' z U:= funext fun i=>map_smul _ z (U i)
   map_add' U V:= funext fun i=> map_add _ (U i) (V i)
def boostD (a:Axis)(G: Gauge): Sky G→ₗ[ℂ] Sky G where
   toFun U n:= jaw G n (Motif.A n G (chair n a)) (U n)
   map_add' U V:= funext fun i=> map_add _ (U i) (V i)
   map_smul' z U:= funext fun i=> map_smul _ z (U i)
lemma mood (l:List Axis)(G: Gauge): Present ( E:= Sky G ) (fun z n=>Pole G n i j z l):= by
    induction l with
    | nil=> apply Present.add (Present.here (fun n:ℕ=>F₀ (G:=G) (chair n i) (chair n j))); apply Present.step; exact Present.here _
    | cons a l ih=> exact ( ih.grows (spinD a G)).add ((ih.grows (boostD a G)).step)
end Pole
end YM.MS.Mach
