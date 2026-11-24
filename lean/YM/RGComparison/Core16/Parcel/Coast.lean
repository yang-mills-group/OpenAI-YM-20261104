import YM.RGComparison.Core16.Parcel.Rise
/-!
# Stencil re-expression exact across LOCAL windows

Ties at wrapping addresses go to fixed canonical representative. Really uses POST clocks: no
hypothesis of period large on probability law side (except Larger). Need `T.price` & release, paid later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Parcel.Oven
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Matrix Push.AbsoluteSums.Animals
open Lumen Lumen.Planet PertExtension PertExtension.Series Tested Radial Therm
open Forge Forge.Hut Precision Exterior Push Push.BetaTransport Push.GridApprox Finset
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side}{H:Patch}{K:KernelChoices}
-- recipe choice `(H,K)` independent of period.
variable (K) (P: Oven H)
variable {d : f.val=c.val*H.L.val}
local notation "X0"=>P.stance K
local notation "Y"=> StepData.mk H K d

def listPtr (T : Forest (Y).ratio) (z:Site f) (e:P.Xways) : Option T.Free :=
    let u := lift (e.1 - hold X0 0)
    let j:Edge (Site f):= (wrap f u+z,e.2)
    if u∈Lattice.box (Hut.width H) then if h:j∈T.trunks then none else some ⟨j,h⟩ else none
lemma thread (T : Forest (Y).ratio) (z: Site f)(e:P.Xways) {i:T.Free}(hi:listPtr K P T z e= some i) : i∈neighborsOf (pad T) (Hut.width H) z:=by
    unfold listPtr at hi; dsimp only at hi; split at hi; rename_i hv; split at hi; contradiction
    next h => rw [←Option.some.inj hi]; exact (member ..).2 (box_sep (Set.mem_image_of_mem (fun x=> wrap f x+z) hv))
    next h=> contradiction

-- This fill is independent of `q∈T`; no meas condition of `T`. Bump uses same inside & outside release.
def loans (T : Forest (Y).ratio)(z:Site f)(x:Sky G T.Free) : (P.Xways → G.Color):=portrait (listPtr K P T z) (fun i=> G.curvature (x i))
local notation "R"=> Hut.width H
lemma slip {x:Cover}(h:x∈Lattice.box R): lift (wrap P.floor x)=x:=by
    refine lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩; have he:= (box_test.mp h).1 i; have hu:= (box_test.mp h).2 i; have hd:=P.house; omega
lemma tipfill {T:Forest (Y).ratio}{δ:ℝ}{z:Site f}{x: Sky G T.Free}(U:Point G P.Xways)(hU: U.2= loans K P T z x) (h:crisp δ (neighborsOf (pad T) R z) x)(he:∀v:G.El,G.chord v<δ→ launch (G.curvature v)=v){u:Cover}(hu:u∈Lattice.box R)(j:Axis):
    expandAt z (T.drape x) (u,j)=expandAt (hold X0 0) (P.lamp U) (u,j):=by
    let q:Edge (Site f):= (wrap f u+z,j); let p:P.Xways:=(wrap P.floor u+hold X0 0,j)
    have hh : lift (p.1 - hold X0 0)= u:= by unfold p; rw [show (wrap P.floor u+hold X0 0,j).1= _ from rfl]; change lift (wrap P.floor u+hold X0 0-_) =_; rw [add_sub_cancel_right]; exact slip P hu
    change T.drape x q= launch (U.2 p); rw [hU,loans,portrait]; by_cases hz:q∈ T.trunks
    · rw [show listPtr K P T z p=none from ?_]; rw [show T.drape x q=1 from T.on_tree _ ⟨q,hz⟩]; exact launch_zero.symm
      unfold listPtr; simp only [hh,hu, ↓reduceIte]; exact dif_pos hz
    let w:T.Free:=⟨q,hz⟩; have hwz : listPtr K P T z p=some w:=by unfold listPtr; dsimp only; rw [hh]; exact (if_pos hu).trans (dif_neg hz)
    rw [show T.drape x q=x w from T.off_tree x w,hwz]; exact (he _ (h w (thread K P T z _ hwz))).symm

def clasp (U V:CoverConfig G)(v:ℕ) := ∀ x∈Lattice.box v,∀ i : Axis,U (x,i)=V (x,i)

private lemma glued (P : Patch){U V:CoverConfig G}(h:clasp U V (Hut.width P)) {Z:Set Cover}(hi:∀x∈Z,x∈Lattice.box (Hut.width P)): Agrees Z U V:=fun i h' _=>h i.1 (hi _ h') _
-- touches inside ball; use cover, not torus.
private lemma visited {x:Cover}{r:ℕ}(hx:x∈Lattice.box r){y:Cover}(l:Walk)(h:y∈visits x l):y∈Lattice.box (r+l.length):=by
    induction l generalizing x r with
    | nil=> rwa [List.mem_singleton.mp h]; -- cast
    | cons d l ih=>
      rcases List.mem_cons.mp h with e|e
      · subst e; exact box_larger hx (by omega)
      apply box_larger (ih (r:=r+1) (show _ from ?_) e); rotate_left
      · obtain ⟨h,h'⟩:=box_test.mp hx; apply (box_test (r:=r+1)).mpr; constructor <;> intro i <;> have h₁:=h i <;> have h₂:=h' i <;> (rcases d with ⟨j,_|_⟩ <;> by_cases he:i=j <;> simp [Step.vec,he] at * <;> omega)
      simp; omega
private lemma clasp_walk {U V:CoverConfig G} {x:Cover}{r k:ℕ}(l:Walk)(he:clasp U V k)(h:x∈Lattice.box r)(ht:r+l.length≤k): travel U x l=travel V x l:=by
    apply travel_local
    intro i hi _ ; change i.1∈visits x l at hi; exact he _ (box_larger (visited h l hi) ht) _
set_option maxHeartbeats 350000 in
lemma portAccess (p:PlaqAxes){U : Config G f}{V : Config G P.floor}{z:Site f}(h:clasp (expandAt z U) (expandAt (hold X0 0) V) R) : faceValue U (z,p)=faceValue V (hold X0 0,p):=by
    let w:= Lattice.square p.val.1 p.val.2; have hx : 4≤R:=by have hk : 1≤H.L.val := H.L.property; unfold Hut.width; unfold macroR; omega
    suffices he : travel (expandAt z U) 0 w= travel (expandAt (hold X0 0) V) 0 w by simpa only [travel_at,map_zero,zero_add] using! he
    exact clasp_walk (U:=expandAt z U) (V:=expandAt (hold X0 0) V) w h (r:=0) (center_box 0) (by dsimp [w,square]; omega)

-- account upper connector start frame & finish frame even on the SAME key.
lemma ticketShift {x:Cover} (h:x∈Lattice.box (reach H))(j:Axis): x+centerRoot H (step j)∈Lattice.box R:=by
    obtain ⟨h1,h2⟩:=box_test.mp h; apply box_test.mpr
    unfold centerRoot; constructor <;> intro i <;> specialize h1 i <;> specialize h2 i <;> by_cases he:j=i <;> simp [Lattice.step_apply,he, eq_comm] <;> unfold Hut.width <;> omega
lemma carries {U : Config G f}{V:Config G P.floor}{z:Site c} (hK:H.Branches K G) (h:clasp (expandAt (hold Y z) U) (expandAt (hold X0 0) V) R) {j:Axis}
    (s:(Y).SitesChoice) (t:(X0).SitesChoice)(hs:s z=t 0)(ht:s (z+step j)=t ((0:Site P.roof)+step j)) : (Y).connector U s (z,j)=(X0).connector V t (0,j):=by
    let X:= expandAt (hold Y z) U; let X':= expandAt (hold X0 0) V; let d':= centerRoot H (step j)
    have hr : Agrees (Lattice.box (reach H):Set Cover) X X':= glued H h fun x hx=> box_larger (show x ∈ Lattice.box _ from hx) (by unfold Hut.width; omega)
    have he : Agrees (Lattice.box (reach H):Set Cover) (Lattice.translate d' X) (Lattice.translate d' X'):=fun i hi _=> h _ (ticketShift (show _ from hi) j) _
    have hx : expandAt (hold Y (z+step j)) U=Lattice.translate d' X:=by simpa [Pressure.plank,add_comm] using! levels Y z U (step j)
    have hy : expandAt (hold X0 ((0:Site P.roof)+step j)) V=Lattice.translate d' X':=by simpa [Pressure.plank] using! levels X0 0 V (step j)
    let li:=List.replicate H.L.val (posDir j)
    have hk (x:H.Points): travel X x.val li=travel X' x.val li:=by
       apply clasp_walk li h (show x.val∈Lattice.box H.radius from x.property); rw [show li.length=H.L.val from List.length_replicate]; unfold Hut.width Push.GridApprox.reach; omega
    funext i; unfold StepData.connector StepData.frames; change H.frame K X (s z) i *_ * (H.frame K (expandAt (hold Y (z+step j)) U) (s _) i)⁻¹ = H.frame K X' _ i * travel X' i.val li * (H.frame K (expandAt (hold X0 ((0:Site P.roof)+step j)) V) _ i)⁻¹
    rw [hx,hy,hs,ht,(patch_dep H hK _ hr).1,(patch_dep H hK _ he).1]; exact congr_arg (fun v=>_* v * _) (hk i)
end YM.RGComparison.Core16.Parcel.Oven
