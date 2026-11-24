import YM.MS.Wilson.Space
import YM.MS.Bare.Running
import YM.MS.Cylinder.APeriod
import YM.MS.Properties

/-!
# Real leg lattice

Leg uses `Branch`. This only works Axis four on Wilson side. Take arities
 later from the chosen Gauge remset. The period case doesn't change units.
   Low Q identities should see the full position ghosts and harmonics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau
open Function Filter Finset Set Koszul Plane Cylinder Lab Taylor Complex
open scoped Topology ContDiff
abbrev Stem (B C:Type*) := Sum (B×C) C
variable {D C:Type*}
def signA (u:Bool): Stem D C → Leg D C| Sum.inl (i,x)=> ((some i,u),x)| Sum.inr c=> ((none,u),c)
lemma signA_rec (u:Bool) : Injective (signA u (D:=D) (C:=C)):= by rintro (⟨_,_⟩|i) (⟨_,_⟩|j) h <;> simp_all [signA]
def leggin : Bonded (Landau.parity (A:=D) (C:=C)) (Stem D C) where
   plain:= ⟨signA false, signA_rec false⟩
   dual:=⟨signA true, signA_rec true⟩
   diff i j:=by rcases i with ⟨_,_⟩|i <;> rcases j with ⟨_,_⟩|j <;> simp [signA]
   wave i:= by rcases i with ⟨_,_⟩|i <;> simp [signA,p,parity]
end YM.MS.Landau
namespace YM.MS.Native
open Function Filter Finset Set Koszul Plane Lattice Cylinder Lab Taylor Bare Landau
open scoped Topology ContDiff
variable (G:Gauge)
abbrev ToneS := Stem Axis (Conn G)
abbrev Spectrum := leggin (D:=Axis) (C:=Conn G)
variable (P:Type)
abbrev Mind := Edge P × Conn G
abbrev LightMode := Note G Axis P
abbrev Film := Score G Axis P
abbrev Dot := Seed (Branch G Axis) P ℂ
abbrev Paper := Spectrum G |>.district (P:=P)
variable {G P}
def why (i : ToneS G × P) : Mind G P ⊕ Eyes G P := match i with
   | (Sum.inl (a,k),x) => Sum.inl ((x,a),k)
   | (Sum.inr k,x)=> Sum.inr (x,k)

def panelIndex (G:Gauge)(P:Type): (Mind G P ⊕ Eyes G P) ≃ (ToneS G ×P) where
    toFun i:= match i with
    | Sum.inl ((x,a),i)=> (Sum.inl (a,i),x)
    | Sum.inr (x,i)=> (Sum.inr i,x)
    invFun := why
    left_inv i:= by rcases i with ⟨⟨_,_⟩,_⟩|⟨_,_⟩ <;> rfl
    right_inv i:= by rcases i with ⟨_|_,_⟩ <;> rfl

def panel (G:Gauge)(P:Type) : Focus (Paper G P) (Mind G P) (Eyes G P) where
   call := panelIndex G P
   act i:= by rcases i with ⟨⟨x,a⟩,i⟩; rfl
   gauge i:=by rcases i; rfl

def formAt (a:Axis)(i:G.ColorIndex)(x:P): LightMode G P:= ((Landau.gauge a,i),x)
def ghostAt (i:G.ColorIndex)(x:P): LightMode G P:= ((ghost,i),x)
lemma panelA (i:Mind G P): (Paper G P).plain ((panel G P).AId i)= formAt i.1.2 i.2 i.1.1:=rfl
lemma panelK (k:Eyes G P): (Paper G P).plain ((panel G P).KId k)=ghostAt k.2 k.1:= rfl
lemma feeA (i:Mind G P): (Paper G P).fee ((panel G P).AId i)=(1:ℂ):= rfl
lemma feeK (k:Eyes G P): (Paper G P).fee ((panel G P).KId k)=(-1:ℂ):= rfl

-- Physical directions and compact link projections
variable (G)
variable {G}
variable {Q:Type*} [DecidableEq Q]

section
variable [Fintype Q]
-- all frame recon. Keep notation Π.W.
end
section
variable [DecidableEq P]
def direction : LightMode G P→Lot G (Edge P)
    | (( (some a,false),i),x)=> priv ((x,a),i)
    | _=> 0
lemma dirA (i:Mind G P): direction ((Paper G P).plain ((panel G P).AId i))= priv i := rfl
variable [Fintype P]
def glow (G:Gauge)(P:Type)[DecidableEq P][Fintype P]: Focus.Glow (panel G P) (Lot G (Edge P)) where
    e0:= direction
    seed := projector
    restore v:= by simp_rw [dirA]; exact frame v
    ever i:= by
       rcases i with ⟨⟨⟨_|a,_|_⟩,i⟩,x⟩ <;> try exact fun h=>(h rfl).elim
       exact fun _=> ⟨((x,a),i),rfl⟩
def reads (f:Lot G (Edge P)→ℝ): Film G P:= ink direction f
end
end YM.MS.Native
