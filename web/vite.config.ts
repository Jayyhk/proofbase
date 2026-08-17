import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

export default defineConfig({
  plugins: [react()],
  server: {
    proxy: {
      '^/(proofs|health|versions|declarations|compile)': 'http://localhost:5000',
    },
  },
})
