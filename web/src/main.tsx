import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import './index.css'
import App from './App.tsx'

// mount the react app into <div id="root"> in index.html.
// StrictMode runs each useEffect twice in dev. Stripped in prod.
createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <App />
  </StrictMode>,
)
