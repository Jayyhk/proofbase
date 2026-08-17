// the shared frame for every popup.
// outer div = the greyed out backdrop.
// inner div = the white box. stopPropagation keeps clicks inside the box from counting as a backdrop click.
// children = things between <Modal> and </Modal>.
export default function Modal(props: { onClose: () => void; children: React.ReactNode }) {
  return (
    <div className="modal-backdrop" onClick={props.onClose}>
      <div className="modal" onClick={(e) => e.stopPropagation()}>
        <button className="panel-close" onClick={props.onClose}>×</button>
        {props.children}
      </div>
    </div>
  )
}
