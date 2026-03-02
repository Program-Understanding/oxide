import {
  CategoryScale,
  Chart as ChartJS,
  Legend,
  LinearScale,
  LineElement,
  PointElement,
  Tooltip,
  BarElement,
  LogarithmicScale,
} from "chart.js";
import zoomPlugin from "chartjs-plugin-zoom";
import { MatrixController, MatrixElement } from "chartjs-chart-matrix";

let registered = false;

export function ensureChartJsRegistered() {
  if (registered) return;

  ChartJS.register(
    LineElement,
    PointElement,
    CategoryScale,
    LinearScale,
    LogarithmicScale,
    BarElement,
    Tooltip,
    Legend,
    zoomPlugin,
    MatrixController,
    MatrixElement,
  );

  registered = true;
}
