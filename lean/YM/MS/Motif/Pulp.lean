import YM.MS.Motif.Plateau

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Native
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ}
def δ (a:Arts.L n) : SectorP n→+ℂ:= AddMonoidHom.mk' (fun x=>Complex.I * (x a:ℂ)) (fun x y=>by change Complex.I*((x a+y a:ℝ):ℂ)=_; push_cast; ring ) -- mk'
abbrev rowP (a:Arts.L n): Op ( Shore G n ) ℂ:= moment (δ a)
abbrev axisP (a:Arts.L n) : Mield G n→ₗ[ℂ] Mield G n:= forge (rowP a)
def lip (b:Bool) (a:Option ( Arts.L n )) : Mield G n:= fun c=> leaf ( onX b (a,c))
def A (n:ℕ)(G:Gauge)(i:Arts.L n) : Mield G n:= lip false (some i)
def cwave (n:ℕ)(G:Gauge): Mield G n:= lip false none
def convoke (z:ℂ)(a:Arts.L n) : Mield G n→ₗ[ℂ] Mield G n:= axisP a+ z • jaw G n ( A n G a )
def F₀ (a b:Arts.L n) : Mield G n:= axisP a ( A n G b ) - axisP b ( A n G a)
def cur (z:ℂ)(a b:Arts.L n): Mield G n:= F₀ a b+ z • jaw G n ( A n G a ) ( A n G b )
def Sc (z:ℂ)(G:Gauge)(n:ℕ): Mield G n:= (-z/2:ℂ) • jaw G n (cwave n G) ( cwave n G)
def applyS (z:ℂ)(G:Gauge)(n:ℕ): Chan G n→ Rack G n
 | (none,i)=> Sc z G n i
 | (some a,i)=> convoke z a (cwave n G) i
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
def sume (F H:Mield G n): Rack G n:= ∑ i:G.ColorIndex, bite n G (F i) ( H i )
local notation "g"=> cwave n G
local notation "Ω" => jaw G n
lemma realA (a:Arts.L n): Mood false (A n G a):= ⟨ fun i=> note_p (p:=parity) ( onX false ( some a,i)) (fun _=>(1:ℂ)), fun i=> section_n (G:=G) (some a,i) (fun _=>1) ⟩ -- note_p p implicit ? Fint
lemma ghMd : Mood true ( cwave n G ):= ⟨fun i=> note_p (p:= parity) (onX false (none,i)) (fun _=> (1:ℂ)), fun i=> section_n (n:=n) (none,i) (fun _=>1)⟩
variable (z:ℂ)
lemma heatSA (b:Bool)(u:Mield G n)(h:Mood b u)(a:Arts.L n): Mood b (convoke z a u):= by rw [convoke,LinearMap.add_apply,LinearMap.smul_apply]; cases b <;> exact (h.moment (δ a)).add ((realA a|>.jawn h).smul z)
lemma curs (a b:Arts.L n): Mood (G:=G) false (cur z a b):=( ( ( realA b ).moment (δ a) ).sub (realA a |>.moment (δ b))).add (( realA a |>.jawn ( realA b )).smul z)
lemma Shc : Mood false (Sc z G n):= ( ghMd.jawn ghMd ).smul _
lemma application : Lamp (applyS z G n):= by constructor <;> rintro ⟨_|a,i⟩; exacts [Shc z |>.tune i, heatSA z _ _ ghMd a|>.tune i,Shc z|>.rank i,heatSA z _ _ ghMd a|>.rank i]
local notation "σ" => dot (applyS z G n)
local notation "Sg" => forge σ
lemma S_action (a: Arts.L n) : Sg (A n G a)=convoke z a g:= funext fun i=> dot_call ( some a,i)
variable {u:Mield G n} {b:Bool}
lemma comm_d (s:Arts.L n) : Sg (axisP s u)=axisP s ( Sg u):= funext fun _=> dot_moment (δ s)
lemma deriv_v (h:Mood b u)(H:Mield G n): Sg (Ω u H)= Ω (Sg u) H + (cross true b:ℂ) • Ω u (Sg H):= derive h.tune (application z)
lemma S_D (a:Arts.L n) : Sg ( convoke z a u)= convoke z a ( Sg u) + z • Ω (convoke z a g) u:= by simp only [convoke,LinearMap.add_apply, map_add,LinearMap.smul_apply,map_smul,comm_d, deriv_v z (realA a), cross_false',one_smul, S_action]; rw [smul_add]; abel
end YM.MS.Motif
