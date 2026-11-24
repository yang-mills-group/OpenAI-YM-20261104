import YM.OPE.Compatible.Parch.Lop
/-!
# Stations and arc visits
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}
section
-- paths certificate
structure Prom (S:Finset Cover)(o:Cover)(n:ℕ) where
        voyage (x:↥S):Walk
        base : o∈S
        ends (x):stop o (voyage x)=x.val
        miles (x):(voyage x).length≤ n
        sites (x):∀ y∈Lattice.visits o (voyage x),y∈S
lemma stadium (b:ℕ)(o:Cover)(hx:o∈Lattice.box b) : Nonempty (Prom (Lattice.box b) o (10*b)):=by
        choose V he hv ht using fun i:↥(Lattice.box b)=> (hall o _ hx i.property).sees; exact ⟨⟨V,hx,he,hv,ht⟩⟩
lemma Aurora (h:r<b):Nonempty (Prom (galaxy r b) (anchorX b) (40*b)):=by
        choose V he hv ht using fun i:↥(galaxy r b)=> ((spaced h _ i.property).2).sees; exact ⟨⟨V,roc h,he,hv,ht⟩⟩
section
namespace Prom
variable {o:Cover}(P:Prom S o b)
def firstB(e:↥(crossV S)): ↥S:=⟨e.val.1,(cross_def e.val).1 e.property|>.1⟩
def upperB(e:↥(crossV S)):↥S:=⟨dotUp e.val,(cross_def e.val).1 e.property|>.2⟩
noncomputable def ringL (e:↥(crossV S)): Walk:= (P.voyage (firstB e)++ [posDir e.val.2])++Lattice.reverse (P.voyage (upperB e)) -- parentheses
lemma closer (e:↥(crossV S)): stop o (P.voyage (firstB e)++[posDir e.val.2])=(upperB e).val:=by rw [stop_append,P.ends];rfl
lemma trip (e:↥(crossV S)): stop o (P.ringL e)=o:=by rw [ringL,stop_append, P.closer,← show stop o (P.voyage (upperB e))= _ from P.ends _, Lattice.reverse_stop]
lemma via (e:↥(crossV S)): (P.ringL e).length ≤ 2*b+1:=by rw[ringL,List.length_append,List.length_append,show [posDir e.val.2].length=1 from rfl,Lattice.reverse,List.length_map,List.length_reverse]; have hz:= P.miles (firstB e); have hv:=P.miles (upperB e); omega
lemma trough (x:↥S): Lattice.LocalOn (↑S) (fun U: CoverConfig G=>travel U o (P.voyage x)):= by intro U V h; exact travel_local o (P.voyage x) U V (fun p hv he=> h p (P.sites x _ hv) (P.sites x _ he))
lemma readC (e:↥(crossV S))(U: CoverConfig G): travel U o (P.ringL e)=travel U o (P.voyage (firstB e))* U e.val *(travel U o (P.voyage (upperB e)))⁻¹:=by
       rw [ringL,travel_append, P.closer, travel_append, P.ends,← show stop o (P.voyage (upperB e))= _ from P.ends _,travel_reverse]; rw [travel,travel,mul_one]; rfl
lemma coreK (U V: CoverConfig G)(he:Agrees S U V)(e:↥(crossV S)):travel U o (P.ringL e)=travel V o (P.ringL e):=by rw [P.readC,P.readC,show travel U o (P.voyage (firstB e))=_ from P.trough _ U V he,show travel U o (P.voyage (upperB e))=_ from P.trough _ U V he,he e.val (firstB e).property (upperB e).property]
end Prom
end
-- insertion chart
noncomputable def TipP (G:Gauge)(S:Finset Cover)(x:Libra.Tile G (crossV S)):CoverConfig G:= fun i=>if h:i∈crossV S then x ⟨i,h⟩ else 1
lemma senses (x:Libra.Tile G (crossV S))(i:↥(crossV S)):TipP G S x i.val=x i:=dif_pos i.property
noncomputable def lobK (G:Gauge)(S:Finset Cover) (x: Libra.Keys G (crossV S)):CoverConfig G:= TipP G S (put x)
lemma glowQ (x: Bid.Dir G n)(y:Site n) :Agrees (↑S) (expandAt y (represent x)) (lobK G S (dip (fun i:↥(crossV S)=>i.val) n y x)):=by
        intro e he hy; let q:↥(crossV S):= ⟨e,(cross_def e).mpr ⟨he,hy⟩⟩; let T:=dip (fun i:↥(crossV S)=>i.val) _ y (G:=G); unfold lobK; rw [show TipP _ _ _ e= put (T x) q from senses (put (T x)) q,expandAt,arkL]; rw [add_comm]; rfl
end
end YM.OPE.Merchant
